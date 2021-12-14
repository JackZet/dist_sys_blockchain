package main

import (
	"bufio"
	"bytes"
	"crypto/rand"
	"crypto/sha256"
	"encoding/gob"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"math/big"
	"net"
	"os"
	"reflect"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

type Ledger struct {
	Accounts map[string]int
	lock     sync.Mutex
}

type ToSend struct {
	IPAndPort    string
	Peers        []string
	Trans        SignedTransaction
	Block        Block
	GenesisBlock GenesisBlock
}

type SendTransaction struct {
	Trans SignedTransaction
}

type SendIPAndPort struct {
	IPAndPort string
}

type SendPeers struct {
	Peers []string
}

type PublicKey struct {
	N *big.Int
	E *big.Int
}

type PrivateKey struct {
	N *big.Int
	D *big.Int
}

type Sequencer struct {
	SeqPublicKey *PublicKey
}

type Block struct {
	BlockID           string
	VerificationKey   string
	PreviousBlockHash []byte
	PreviousBlock     *Block
	Slot              int
	Transactions      []SignedTransaction
	Draw              string
	Signature         string
}

type GenesisBlock struct {
	Seed      int
	InitialID [10]string
	PKtoSKmap map[*PublicKey]*PrivateKey
	ToHash    string
}

//Mapping from whether a transaction has already been sent
var transactionMap = make(map[string]SignedTransaction)
var sequencedTransactions []SignedTransaction
var transactionQueue []SignedTransaction
var aliasMap = make(map[string]string)
var broadcastedBlocksPeer []string
var pkToSkMap = make(map[*PublicKey]*PrivateKey)
var initialID [10]string

// The ledger object to keep track of accounts and their balances.
var ledger *Ledger
var peers []string
var mutex = &sync.Mutex{}
var ownIP string
var connections []net.Conn
var B int = 3
var dialConns []string
var pk *PublicKey
var sk *PrivateKey
var receivedGenesisBlock bool
var SEED int = 45
var HARDNESS, _ = big.NewInt(1).SetString("110463994589449747285402016673771719149532991672595109738822075371042551319525412398", 10)
var SLOTLENGTH = time.Second * 1
var gBlock GenesisBlock
var currentBlockHash []byte
var slot int
var mining bool = true
var receivedFirstBlockAfterGenesis = false
var lastSeenBlock *Block

func MakeLedger() *Ledger {
	ledger := new(Ledger)
	ledger.Accounts = make(map[string]int)
	return ledger
}

type SignedTransaction struct {
	ID        string // Any string
	From      string // A verification key coded as a string
	To        string // A verification key coded as a string
	Amount    int    // Amount to transfer
	Signature string // Potential signature coded as string
}

func (l *Ledger) SignedTransaction(t *SignedTransaction) {
	l.lock.Lock()
	defer l.lock.Unlock()

	if t.Amount < 0 {
		fmt.Println("---------------------Amount cannot be negative. No transaction was made-----------------")
		return
	}

	//This is a []byte version of the locally generated hashed message
	hashForSignature := hashForTransactionSignature(t.ID, t.From, t.To, t.Amount)

	//This is a big int version of the locally generated hashed message
	hashForSignatureBigInt := big.NewInt(1).SetBytes(hashForSignature)

	//This is a big.int of the received signature
	signatureBigInt := big.NewInt(1).SetBytes([]byte(t.Signature))

	//Gets senders public key
	senderPK := new(PublicKey)
	senderPK, _ = dec(t.From, true)

	//This is a big int of the unsigned signature
	decodedSignature := authenticate(senderPK, signatureBigInt)

	//This is verification of the unsigned signature and the hashed message
	validSignature := verify(decodedSignature, hashForSignatureBigInt)

	//validSignature := verify(signatureBigInt, hashForSignatureBigInt, senderPK)

	if validSignature {
		l.Accounts[t.From] -= t.Amount
		l.Accounts[t.To] += t.Amount
		fmt.Println("------------------------------Transaction successful!---------------------------------")
		// Print the transaction to the user
		log.Println("New transaction has been made:")
		log.Printf("%s -> %d -> %s\n", t.From, t.Amount, t.To)
		log.Printf("%s has %d, %s has %d\n", t.From, ledger.Accounts[t.From], t.To, ledger.Accounts[t.To])
	} else {
		fmt.Println("---------------------Key was rejected. No transaction was made-----------------")
	}
}

//Creates a GenesisBlock with 10 starting accounts with 10^6 AU
func createGenesisBlock(seed int) GenesisBlock {

	// Set receivedGenesisBlock to true so that we don't also receive it
	receivedGenesisBlock = true

	//temp
	gb := GenesisBlock{}
	var idList [10]string

	for i := 0; i < 10; i++ {

		// Generates initial key pairs for 10 accounts
		pk, sk := keyGen(258)

		// Put 10^6 AU's into their accounts
		ledger.Accounts[enc(pk, nil)] = 1000000

		//Prints
		fmt.Printf("Legit Peer no. %d", i)
		fmt.Println()
		fmt.Printf("Public key: (%s, %s)", pk.E.String(), pk.N.String())
		fmt.Println()
		fmt.Printf("Secret key: (%s,  %s", sk.D.String(), sk.N.String())
		fmt.Println()

		// ID list is a list of the string encoded public keys
		idList[i] = enc(pk, nil)

		//Maps the public key to the secret key for easier test access
		pkToSkMap[pk] = sk
	}

	// Set genesis block fields
	gb.Seed = seed
	gb.InitialID = idList
	gb.PKtoSKmap = pkToSkMap
	gb.ToHash = "genesisblock"
	return gb
}

func test() {
	public := pk
	secret := sk
	transIDbigInt, err := rand.Int(rand.Reader, big.NewInt(10000))
	if public == nil || secret == nil {
		fmt.Println("Public and secret keys are nil. Retrieve keys  before testing")
	}
	if err != nil {
		fmt.Println("There was an error making random big int")
		fmt.Println(err.Error())
	}

	transID := transIDbigInt.String()
	amount := 10
	signature := string((sign(secret, big.NewInt(1).SetBytes(hashForTransactionSignature(transID, enc(public, nil), enc(pk, nil), amount)))).Bytes())
	trans := SignedTransaction{transID, enc(public, nil), enc(pk, nil), amount, signature}
	sendTransactionToAllConns(trans)
}

// Starts to compute draws
func participateInLottery(pk *PublicKey, sk *PrivateKey) {

	fmt.Println("Participating in lottery... Picking draws...")
	slot = 0
	for mining {
		//H(Lottery, Seed, slot, vki, Draw)
		draw := createDraw(sk, SEED, slot)
		block := Block{}
		block.VerificationKey = enc(pk, nil)
		block.Slot = slot
		block.Draw = draw.String()

		if verifyHardness(block) {
			fmt.Println("------------------WE WON THE LOTTERY-------------------")

			// Create the block with the winning draw

			block = createBlockWithWinningDraw(block, sk)
			fmt.Println("------------------SENDING BLOCK-------------------")
			//Broadcast the block
			broadcastBlock(block)
			verifyDraw(block)

			fmt.Printf("Sent a block with id: %s \n slot: %d", block.BlockID, slot)
			fmt.Println()
		}
		// Sleep for 1 second and increment slot
		time.Sleep(SLOTLENGTH)
		slot++
	}
	fmt.Println("Quit the lottery... Stopped picking draws...")
}

func keyGen(k int) (*PublicKey, *PrivateKey) {

	//Initaliazing structs
	pk := new(PublicKey)
	sk := new(PrivateKey)
	e := new(big.Int).SetInt64(3)
	n := new(big.Int)
	d := new(big.Int)

	//Divide k by 2
	i := k / 2

	//Produces prime p with bit-lenght i
	p, err := rand.Prime(rand.Reader, i)
	if err != nil {
		fmt.Println("Theres was an error finding p")
	}
	//Produces prime q with bit-lenght i
	q, err := rand.Prime(rand.Reader, i)
	if err != nil {
		fmt.Println("Theres was an error finding p")
	}
	//n = p*q
	n.Mul(p, q)

	one := new(big.Int).SetInt64(1)
	x := new(big.Int)
	//Subtract 1 from p, q
	p.Sub(p, one)
	q.Sub(q, one)
	x.Mul(p, q)

	//mod inverse
	if d.ModInverse(e, x) == nil {
		return keyGen(k)
	}
	//We assign our keys the values
	pk.N = n
	pk.E = e
	sk.N = n
	sk.D = d

	return pk, sk
}

func authenticate(pk *PublicKey, signature *big.Int) *big.Int {

	//Gets value from public key
	n := pk.N
	e := pk.E
	m := new(big.Int)

	//Decrypts the signature with the public key
	m.Exp(signature, e, n)
	return m
}

//Verifies if the two big ints are equal
func verify(sentSign *big.Int, receivedSign *big.Int) bool {
	fmt.Println(receivedSign.String())
	if sentSign.Cmp(receivedSign) == 0 {
		return true
	}
	return false
}

// Creates the whole block after computing a winning draw
func createBlockWithWinningDraw(block Block, sk *PrivateKey) Block {

	fmt.Println("initializing block creating process...")
	var list []SignedTransaction
	mutex.Lock()
	for _, trans := range transactionQueue {
		list = append(list, trans)
	}
	mutex.Unlock()

	//Sort the list of Transaction IDs and append it to the block
	//sort.Strings(list)

	// Computing random blockID
	bigIntRandom, _ := rand.Int(rand.Reader, big.NewInt(10000000))
	blockID := strconv.FormatInt(bigIntRandom.Int64(), 10)

	block.BlockID = blockID
	block.Transactions = list

	mutex.Lock()
	if lastSeenBlock != nil {
		block.PreviousBlock = lastSeenBlock
	}
	mutex.Unlock()

	//Generate Signature for block and append it
	hash := hashForBlockSignature(block)
	hashBigInt := big.NewInt(1).SetBytes(hash)
	signature := sign(sk, hashBigInt).Bytes()
	block.Signature = string(signature)

	//Reset transaction queue
	mutex.Lock()
	transactionQueue = nil
	//sequencedTransactions = nil
	mutex.Unlock()

	return block
}

// Broadcasts the given block
func broadcastBlock(block Block) {
	for _, loopConn := range connections {
		// Send the Block to the peer through gob.
		gob.NewEncoder(loopConn).Encode(createToSendObject("", nil, SignedTransaction{}, block, GenesisBlock{}))
	}
}

// Broadcasts the genesis block
func broadcastGenesisBlock(gBlock GenesisBlock) {
	for _, loopConn := range connections {
		// Send the genesis to the peers through gob.
		gob.NewEncoder(loopConn).Encode(createToSendObject("", nil, SignedTransaction{}, Block{}, gBlock))
	}
}

//Listens for connections
func listenforPeer(conn net.Conn) {
	ln, _ := net.Listen("tcp", ":")
	defer ln.Close()

	//Finds local ip4
	getLocalIPv4(ln)
	fmt.Println("Listening on " + ownIP)
	if conn == nil {
		if len(peers) == 0 {
			peers = append(peers, ownIP)
		}
	} else {
		connections = append(connections, conn)
		dialConns = append(dialConns, conn.RemoteAddr().String())
		go peerRead(conn)
	}
	go peerWrite()

	for {
		conn, _ := ln.Accept()
		fmt.Println("Got a connection...")
		connections = append(connections, conn)

		go peerRead(conn)
		sendPeerListToPeer(conn)
	}
}

// Gets local IPv4
func getLocalIPv4(ln net.Listener) string {
	_, port, _ := net.SplitHostPort(ln.Addr().String())
	name, _ := os.Hostname()
	addrs, _ := net.LookupIP(name)
	for _, addr := range addrs {
		if ipv4 := addr.To4(); ipv4 != nil {
			ip := addr.String()
			ownIP = ip + ":" + port
		}
	}
	return ownIP
}

//Sets starting balance for account
func setStartingCredit(public *PublicKey, startingCredit int) {
	mutex.Lock()
	ledger.Accounts[enc(public, nil)] = startingCredit
	mutex.Unlock()
}

func addNewPeerToPeersList(peer string) {
	// Lock the mutex before changing the peers list.
	mutex.Lock()
	// Add new peer to peers list.
	peers = append(peers, peer)
	// Sort the list.
	sort.Strings(peers)
	// Unlock the mutex to allow other goroutines to make changes.
	mutex.Unlock()
}

func connectToNextPeers() {
	// Lock the mutex before reading the next peers.
	mutex.Lock()
	nextPeers := getNextPeers()
	mutex.Unlock()

	// Loop through all next peers.
	for _, peer := range nextPeers {
		_, connExists := contains(dialConns, peer)

		// If we have not already connected to this peer.
		if !connExists {
			if len(dialConns) >= B {
				// Return if we have saturated our connections.
				return
			}
			conn, err := net.Dial("tcp", peer)
			if err == nil {
				connections = append(connections, conn)
				dialConns = append(dialConns, conn.RemoteAddr().String())
				// Display that we have dialed a new peer.
				fmt.Printf("Dialed peer at: %s...\n", peer)
				go peerRead(conn)
			} else {
				fmt.Printf("Unable to connect to peer at '%s'\n", peer)
			}

		}
	}
}

// Encode a block and return in []byte
func encBlock(block Block) []byte {
	marshalledBlock, err := json.Marshal(block)
	if err != nil {
		log.Println(err.Error())
	}
	return marshalledBlock
}

//Encode either a public key og a private key to a string using json marshal
func enc(pk *PublicKey, sk *PrivateKey) string {
	if pk != nil {
		marshalledKey, err := json.Marshal(pk)
		if err != nil {
			log.Println(err.Error())
		}
		return string(marshalledKey)
	} else {
		marshalledKey, err := json.Marshal(sk)
		if err != nil {
			log.Println(err.Error())
		}
		return string(marshalledKey)
	}
}

/*
	NOTE: Should probably rewrite this function with a better solution than
		a isPublicKey boolean
*/
// Decode either a public key or a private key to a string using json unmarshal
func dec(key string, isPublicKey bool) (*PublicKey, *PrivateKey) {
	marshalledKey := []byte(key)
	//If we want to decode a public key
	if isPublicKey {
		unmarshalledKey := new(PublicKey)
		err := json.Unmarshal(marshalledKey, unmarshalledKey)
		if err != nil {
			log.Println(err.Error())
		}
		return unmarshalledKey, nil
	}
	//If we want to decode a private key
	unmarshalledKey := new(PrivateKey)
	err := json.Unmarshal(marshalledKey, unmarshalledKey)
	if err != nil {
		log.Println(err.Error())
	}
	return nil, unmarshalledKey
}

func peerWrite() {
	reader := bufio.NewReader(os.Stdin)
	for {
		// Read string from connection

		text, err := reader.ReadString('\n')
		if err != nil {
			return
		}

		// Remove newline from text
		text = strings.TrimSuffix(text, "\n")
		text = strings.TrimSuffix(text, "\r")

		// Check whether command to print peers list.
		if text == "/peers" {
			fmt.Println(peers)
		} else if text == "/conns" {
			fmt.Println(dialConns)
		} else if text == "/test" {
			fmt.Println("Sending 10 credit to your account to a fake account")
			test()
		} else if text == "/start" {
			if pk == nil && sk == nil {
				fmt.Println("Public and secret key not specified")
				continue
			}
			mining = true
			go participateInLottery(pk, sk)
		} else if text == "/stop" {
			mining = false
		} else if text == "/balance" {
			fmt.Println(ledger.Accounts[enc(pk, nil)])
		} else if text == "/ip" {
			if ownIP != "" {
				fmt.Println(ownIP)
			} else {
				fmt.Println("No ip")
			}
		} else if text == "/ready" {
			go broadcastGenesisBlock(createGenesisBlock(45))
		} else if text == "/key0" && len(pkToSkMap) != 0 {
			retrieveKey(0)
		} else if text == "/key1" && len(pkToSkMap) != 0 {
			retrieveKey(1)
		} else if text == "/key2" && len(pkToSkMap) != 0 {
			retrieveKey(2)
		} else if text == "/key3" && len(pkToSkMap) != 0 {
			retrieveKey(3)
		} else if text == "/key4" && len(pkToSkMap) != 0 {
			retrieveKey(4)
		} else if text == "/key5" && len(pkToSkMap) != 0 {
			retrieveKey(5)
		} else if text == "/key6" && len(pkToSkMap) != 0 {
			retrieveKey(6)
		} else if text == "/key7" && len(pkToSkMap) != 0 {
			retrieveKey(7)
		} else if text == "/key8" && len(pkToSkMap) != 0 {
			retrieveKey(8)
		} else if text == "/key9" && len(pkToSkMap) != 0 {
			retrieveKey(9)
		} else {
			// Split up incoming text at commas.
			splitText := strings.Split(text, ",")

			//Flag is true if there was an error converting
			conversionError := false

			// If there are 7 or 3 parts to the message.
			if len(splitText) == 7 || len(splitText) == 3 {

				//Creating new big ints for conversion
				skD := new(big.Int)
				skN := new(big.Int)
				toE := new(big.Int)
				toN := new(big.Int)
				fromE := new(big.Int)
				fromN := new(big.Int)

				//Making public key placeholders
				to := new(PublicKey)
				from := new(PublicKey)
				secretKey := new(PrivateKey)
				var amount int
				var err1 error
				/* If the user only specifies public key of receiver and an amount,
				we use the terminals secretkey and publickey as default */
				if len(splitText) == 3 {
					secretKey = sk
					from = pk
					to = getToPK(splitText[1])
					amount, err1 = strconv.Atoi(splitText[2])
					if err1 != nil {
						conversionError = true
					}
				} else {
					//Setting user input to big integers
					_, err2 := skD.SetString(splitText[0], 10)
					_, err3 := skN.SetString(splitText[1], 10)
					_, err4 := fromE.SetString(splitText[2], 10)
					_, err5 := fromN.SetString(splitText[3], 10)
					_, err6 := toE.SetString(splitText[4], 10)
					_, err7 := toN.SetString(splitText[5], 10)
					amount, err1 = strconv.Atoi(splitText[6])
					//Conversion error check
					if err1 != nil || err2 != true || err3 != true || err4 != true || err5 != true || err6 != true || err7 != true {
						conversionError = true
					}

					if !conversionError {
						//Setting public keys with big ints
						from.E = fromE
						from.N = fromN
						to.E = toE
						to.N = toN
						secretKey.D = skD
						secretKey.N = skN
					}

				}

				// If error, print correct usage.
				if conversionError {
					fmt.Println("Incorrect transaction format.")
					fmt.Println("Usage: <KEY>,<FROM>,<TO>,<AMOUNT> where KEY -> (d,n) and FROM/TO -> (e,n)")
				} else {

					/*
						NOTE: Not sure if this check should be made locally in peerwrite or remotely on the ledger.
					*/

					//If the account doesnt have enough credit to make transaction
					mutex.Lock()
					overdrawal := ledger.Accounts[enc(from, nil)] < amount
					mutex.Unlock()

					if overdrawal {
						fmt.Println("Not enough credit on the account to make transaction")
						continue
					}

					// Send the transaction to all connections.
					go sendTransactionToAllConns(createSignedTransaction(from, to, secretKey, amount))
				}

			}

		}
	}
}

// Gets the public key from the initialID array for a given string
func getToPK(key string) *PublicKey {
	for i := 0; i < 10; i++ {
		if key == "key"+strconv.Itoa(i) {
			pk, _ := dec(initialID[i], true)
			return pk
		}
	}
	return nil
}

// Sets the retrieved key as the pk and sk global value I.E it is linked to the terminal
func retrieveKey(index int) {
	j := 0
	for key, val := range pkToSkMap {
		if j == index {
			pk = key
			sk = val
			fmt.Println("Key pair received")
			return
		}
		j++
	}
	fmt.Println("Not succesful in retrieving key")
}

//Checks if the terminal input is an alias
func checkForAlias(splitText []string) []string {
	for key, alias := range aliasMap {
		for i := 0; i < len(splitText); i++ {
			if key == splitText[i] {
				splitText[i] = alias
			}
		}
	}
	return splitText
}

func sign(sk *PrivateKey, msg *big.Int) *big.Int {
	//Get values from private key
	s := new(big.Int)
	d := sk.D
	n := sk.N

	//Encrypt the number by signing with our private key
	s.Exp(msg, d, n)
	return s
}

//Function for hashing
func hash(message []byte) []byte {
	sum := sha256.Sum256(message)
	hash := sum[:]
	return hash
}

//Hashing function used as signatures for transactions
func hashForTransactionSignature(transID string, from string, to string, amount int) []byte {
	h := []byte(transID + from + to + string(amount))
	return hash(h)
}

// Computes a hash for the draw before signing
func hashForDraw(seed int, slot int) []byte {
	h := []byte("lottery" + string(seed) + string(slot))
	return hash(h)
}

// Computes the hash for the draw to calculate the value; H(Lottery, Seed, slot, vki, Draw)
func hashForHardnessDraw(block Block) []byte {
	h := []byte("lottery" + string(SEED) + string(block.Slot) + block.VerificationKey + block.Draw)
	return hash(h)
}

func hashForGenesisBlock(gblock GenesisBlock) []byte {
	h := []byte(gblock.ToHash)
	return hash(h)
}

/*
	NOTE: Still need to find a way to append transactions to the hash. For now we leave it out for easier testing.
*/
//Hashing function used as signatures for Blocks
func hashForBlockSignature(block Block) []byte {
	BlockID := block.BlockID
	vk := block.VerificationKey
	previousBlockHash := block.PreviousBlockHash
	slot := block.Slot
	draw := block.Draw
	signature := block.Signature
	h := []byte(BlockID + vk + string(previousBlockHash) + string(slot) + draw + signature)
	return hash(h)
}

//Reads from peer
func peerRead(conn net.Conn) {

	for {
		receivedObject := &ToSend{}
		dec := gob.NewDecoder(conn)
		err := dec.Decode(receivedObject)
		//fmt.Println("Do we get to here?")
		if err == io.EOF {
			fmt.Println("Connection closed by " + conn.RemoteAddr().String())
			return
		}
		if err != nil {
			log.Println(err.Error())
			return
		}

		//If we receive an IP and port that is not our own
		if receivedObject.IPAndPort != "" && receivedObject.IPAndPort != ownIP {
			mutex.Lock()
			_, contained := contains(peers, receivedObject.IPAndPort)
			mutex.Unlock()

			// If it is not already in the Peers list.
			if !contained {
				// Add is to the peers list atomically
				addNewPeerToPeersList(receivedObject.IPAndPort)
				// Announce the new peer
				fmt.Printf("New peer is listening at: '%s'\n", receivedObject.IPAndPort)
				// Broadcast the new peers ip and port
				go broadcastIPAndPort(receivedObject.IPAndPort)

				// Connect to the next known peers.
				go connectToNextPeers()
			}
		}

		// If we have received a peers list
		if receivedObject.Peers != nil {
			// Lock the mutex before chaning the peers list.
			mutex.Lock()
			// Append the new peers list to our peers list.
			peers = append(peers, receivedObject.Peers...)

			//Append yourself
			peers = append(peers, ownIP)

			// Get a list only containing unique peers.
			peers = unique(peers)

			// Sort the peers list.
			sort.Strings(peers)
			// Unlock the mutex to allow other goroutines to make changes.
			mutex.Unlock()

			// Connect to the next known peers.
			go connectToNextPeers()
		}

		if (receivedObject.Trans != SignedTransaction{}) {
			// Write to all known connections
			fmt.Println("POINT 8")
			go sendTransactionToAllConns(receivedObject.Trans)

			mutex.Lock()
			//_, containedInSequencedTransactions := contains2(sequencedTransactions, receivedObject.Trans)
			_, containedInTransactionQueue := contains2(transactionQueue, receivedObject.Trans)
			mutex.Unlock()

			//If the transaction has already been sequenced or if the transaction is already in the queue
			if /*!containedInSequencedTransactions * && */ !containedInTransactionQueue {
				mutex.Lock()
				transactionQueue = append(transactionQueue, receivedObject.Trans)
				fmt.Println("POINT 10")
				mutex.Unlock()
			}
		}

		// If we receive a block
		if !reflect.DeepEqual(receivedObject.Block, Block{}) {

			/*  If the block is not the one we want, we proceed to the next iteration of the loop.
			I.E if the received blocks pointer (hash of it's previous block) is not the same
			as the hash of our current block
			*/
			go broadcastBlock(receivedObject.Block)
			fmt.Println("went here 0")
			ab := acceptBlock(receivedObject.Block)
			fmt.Printf("The block was: %t \n", ab)

		}

		// If we receive a genesis block
		if (!reflect.DeepEqual(receivedObject.GenesisBlock, GenesisBlock{}) && !receivedGenesisBlock) {
			SEED = receivedObject.GenesisBlock.Seed
			receivedGenesisBlock = true
			fmt.Println("--------------RECEIVED GENESIS BLOCK---------------")
			for _, id := range receivedObject.GenesisBlock.InitialID {
				mutex.Lock()
				ledger.Accounts[id] = 1000000
				mutex.Unlock()
			}
			initialID = receivedObject.GenesisBlock.InitialID
			pkToSkMap = receivedObject.GenesisBlock.PKtoSKmap
			currentBlockHash = hashForGenesisBlock(receivedObject.GenesisBlock)
			go broadcastGenesisBlock(receivedObject.GenesisBlock)
		}

	}
}

func verifyBlockString(block Block) {

}

func executeTransactions(transactions []SignedTransaction) bool {

	if len(transactions) == 0 {
		fmt.Println("No transactions in block")
		return true
	}
	for _, trans := range transactions {
		mutex.Lock()
		ledger.SignedTransaction(&trans)
		fmt.Printf("Executed transaction %s", trans.ID)
		mutex.Unlock()
	}
	return true
}

//Verifies that the block is an honest block
func verifyBlock(block Block, receivedFirstBlockAfterGenesis bool) bool {

	/* If it is the block right after genesisblock then do a simple hash compare.
	Else do the normal authentication.
	*/
	if !receivedFirstBlockAfterGenesis {
		mutex.Lock()
		isTheNextBlockWeNeed := bytes.Compare(block.PreviousBlockHash, currentBlockHash)
		mutex.Unlock()
		if isTheNextBlockWeNeed == 0 {
			return true
		}
	} else {
		fmt.Println("Received alleged block")
		computeHashFromReceivedBlock := hashForBlockSignature(block)
		computedHashFromReceivedBlockBigInt := big.NewInt(1).SetBytes(computeHashFromReceivedBlock)
		receivedHashInsideBlockBigInt := big.NewInt(1).SetBytes([]byte(block.Signature))
		pk, _ := dec(block.VerificationKey, true)
		authenticateReceivedHash := authenticate(pk, receivedHashInsideBlockBigInt)
		return verify(computedHashFromReceivedBlockBigInt, authenticateReceivedHash)
	}
	return false
}

// Function that checks if the block has been accepted as the next block in the chain
func acceptBlock(block Block) bool {
	if slot > block.Slot {
		return false
	}
	fmt.Println("went here 1")

	mutex.Lock()
	isTheNextBlockWeNeed := bytes.Compare(block.PreviousBlockHash, currentBlockHash)
	fmt.Println("went here 2")
	mutex.Unlock()

	if isTheNextBlockWeNeed != 0 {
		fmt.Println("not the next block we need")
		return false
	}
	fmt.Println("went here 3")
	if receivedFirstBlockAfterGenesis {
		fmt.Println("received first block after genesis")
		if !verifyBlock(block, true) {
			return false
		}
	} else {
		if !verifyBlock(block, false) {
			return false
		}
	}

	fmt.Println("went here 4")
	if !verifyDraw(block) {
		return false
	}
	fmt.Println("went here 5")
	if !verifyHardness(block) {
		return false
	}

	//Do transcations here
	_ = executeTransactions(block.Transactions)

	mutex.Lock()
	currentBlockHash = []byte(block.Signature)
	mutex.Unlock()

	mutex.Lock()
	lastSeenBlock = &block
	mutex.Unlock()
	fmt.Println("point b")
	return true
}

// Verifies that the draw is honest
func verifyDraw(block Block) bool {

	ComputedHashOfDrawBigInt := big.NewInt(1).SetBytes(hashForDraw(SEED, block.Slot))
	//ReceivedHashOfDraw := big.NewInt(1).SetBytes([]byte(block.Draw))
	ReceivedHashOfDraw := new(big.Int)
	ReceivedHashOfDraw.SetString(block.Draw, 10)
	pk, _ := dec(block.VerificationKey, true)
	authenticateReceivedHashOfDraw := authenticate(pk, ReceivedHashOfDraw)

	return verify(ComputedHashOfDrawBigInt, authenticateReceivedHashOfDraw)
}

// Verifies that the draw won the lottery
func verifyHardness(block Block) bool {

	// Sets  the stake to be the amount of AU on the block sender's account
	mutex.Lock()
	stake := ledger.Accounts[block.VerificationKey]
	mutex.Unlock()

	// Converts int to big int
	stakeBigInt := big.NewInt(1).SetInt64(int64(stake))

	// Computes H(Lottery, Seed, slot, vki, Draw) and stores it as big int
	drawHashBigInt := big.NewInt(1).SetBytes(hashForHardnessDraw(block))

	// Computes the draw value by multiplying the stake with the hash; a * H(Lottery, Seed, slot, vki, Draw)
	value := new(big.Int)
	value.Mul(stakeBigInt, drawHashBigInt)

	// If value is greater than the hardness, we return true
	if value.Cmp(HARDNESS) == 1 {
		return true
	}
	return false
}

// Computes a draw
func createDraw(sk *PrivateKey, seed int, slot int) *big.Int {
	hashOfDraw := hashForDraw(seed, slot)
	drawBigInt := big.NewInt(1).SetBytes(hashOfDraw)
	draw := sign(sk, drawBigInt)
	return draw
}

// Creates a ToSend object
func createToSendObject(IPandPort string, peers []string, transaction SignedTransaction, block Block, gBlock GenesisBlock) ToSend {
	return ToSend{IPandPort, peers, transaction, block, gBlock}
}

//Creates a SignedTransactions object
func createSignedTransaction(from *PublicKey, to *PublicKey, secretKey *PrivateKey, amount int) SignedTransaction {

	// If amount is less than 1
	if amount < 1 {
		fmt.Println("You need to send atleast 1 AU!")
		return SignedTransaction{}
	}

	// If account can't afford transaction fee
	mutex.Lock()
	if ledger.Accounts[enc(from, nil)] < amount-1 {
		fmt.Println("Not enough AU on your account to complete transaction")
	}
	mutex.Unlock()

	// Calculate random transaction id for this transaction.
	bigIntRandom, _ := rand.Int(rand.Reader, big.NewInt(10000))
	transID := strconv.FormatInt(bigIntRandom.Int64(), 10)

	//Computing hash from the fields in SignedTransaction
	signatureHash := hashForTransactionSignature(transID, enc(from, nil), enc(to, nil), amount)

	//We sign the hash
	signaturebigInt := sign(secretKey, big.NewInt(1).SetBytes(signatureHash))

	//We convert the signature to a string
	signature := string(signaturebigInt.Bytes())

	// Instantiate new transaction object.
	return SignedTransaction{transID, enc(from, nil), enc(to, nil), amount, signature}
}

// Sends transaction to all known connections
func sendTransactionToAllConns(trans SignedTransaction) {

	// Return if the transaction has already been sent
	mutex.Lock()
	tmp := transactionMap[trans.ID]
	mutex.Unlock()

	// If the message has already been sent, return
	if (tmp != SignedTransaction{}) {
		fmt.Println("POINT 3")
		return
	}

	// Check whether transaction is contained within the transactions map
	mutex.Lock()
	_, contained := transactionMap[trans.ID]
	fmt.Println("POINT 1")
	mutex.Unlock()

	// If the transaction has not been seen before, we add it to transactionMap
	if !contained {
		mutex.Lock()
		// Put transactionID into the map with the transaction
		transactionMap[trans.ID] = trans
		fmt.Println("POINT 2")
		mutex.Unlock()

	}

	// Create the sendTransaction object from the transaction
	sendTransaction := SendTransaction{trans}
	fmt.Println("POINT 4")

	// Loop over all connections to known peers
	for _, loopConn := range connections {
		// Send the transaction to the peer through gob.
		fmt.Println("POINT 5")
		gob.NewEncoder(loopConn).Encode(sendTransaction)
	}

}

//Returns a list of unique elements
func unique(stringList []string) []string {
	keys := make(map[string]bool)
	list := []string{}
	for _, entry := range stringList {
		if _, value := keys[entry]; !value {
			keys[entry] = true
			list = append(list, entry)
		}
	}
	return list
}

//Broadcasts IPAndPort to all known connections
func broadcastIPAndPort(ipAndPort string) {

	for _, conn := range connections {
		// Send the IP and PORT with gob.
		gob.NewEncoder(conn).Encode(SendIPAndPort{ipAndPort})

	}
}

//Gets list of next peers it should connect to
func getNextPeers() []string {
	var nextPeers []string

	index, contained := contains(peers, ownIP)
	if !contained {
		// Return nil if we have not added our own listen ip and port
		// to our peers list.
		return nil
	}

	for i := 0; i < len(peers); i++ {
		index-- // Do not include self

		// If less than 0, loop back.
		if index <= 0 {
			index = len(peers) - 1
		}
		// End after adding enough peers.
		if len(nextPeers) >= B {
			break
		}

		// Make sure we don't dial self.
		if peers[index] == ownIP {
			continue
		}

		// Don't add already added peers to the list.
		_, contained = contains(nextPeers, peers[index])
		if contained {
			continue
		}

		// Add the peer to the list.
		nextPeers = append(nextPeers, peers[index])
	}
	// Return the next peers.
	return nextPeers
}

//Sends peerlist to a connection
func sendPeerListToPeer(conn net.Conn) {
	gob.NewEncoder(conn).Encode(SendPeers{peers})
}

// Contains method for array of type string
func contains(s []string, e string) (int, bool) {
	for index, a := range s {
		if a == e {
			return index, true
		}
	}
	return 0, false
}

// Contains method for array of type SignedTransaction
func contains2(s []SignedTransaction, e SignedTransaction) (int, bool) {
	for index, a := range s {
		if a == e {
			return index, true
		}
	}
	return 0, false
}

func main() {

	// Create the ledger
	ledger = MakeLedger()

	// Gets input IP
	fmt.Print("Type IP adress and port to connect to (eg. 127.0.0.1:18081)\n")
	reader := bufio.NewReader(os.Stdin)
	remoteIP, _ := reader.ReadString('\n')
	remoteIP = strings.Replace(remoteIP, "\n", "", -1)
	remoteIP = strings.Replace(remoteIP, "\r", "", -1)

	// Dial connection
	conn, err := net.Dial("tcp", remoteIP)

	// Creates an empty genesisblock
	gBlock = GenesisBlock{}

	// Runs this if there was no connection on the input IP
	if err != nil {
		// Print statements
		fmt.Print("There is no peer on " + remoteIP + ". Starting a new network...\n")

	} else {
		// Run this if successfully connect to another peer
		fmt.Println("Succesfully found a peer!")
	}

	// Starts to listen to peer
	listenforPeer(conn)
}
