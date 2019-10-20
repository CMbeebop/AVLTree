
unit AVLTree_u;

{Delphi Implementation of a generic AVLTree -> TAVLTree<TKey>
 Based on the ideas in days 5 and 6 of the Course 6.006 MIT OpenWare

 https://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-006-introduction-to-algorithms-fall-2011/index.htm

 HOW TO USE:
 TKey is a userdefined class that allows for relational operators "<", which is defined
 through a comparison functions that must be provided by the user in the constructor.

 The DS is then built dymanically using insert/remove methods on a Set of Keys S collected
 in a container C. The comparison function must satisfy that no two keys in S are equal,
 to cope with that I usually define a field entityNo on TKey class so all keys have a different
 identifier (see compareMoneyBags in HowToUseExample.pas).

 for a given set of keys S a number of query operations can be performed by te BST : insert,
 remove, successor, predecessor, find, find_min, find_max, extract_min, extract_max, swap, all
 of them with expected time scale O(log|S|), see further comments in the code.

 Other queries allow for extracting a sorted list of keys with all the nodes or just a subset
 Sm \in S with the keys satisfying a condition.
 queries                                           expected time scale
 getSortedListOfKeys,                                    O(|S|)
 getSortedListOfKeysLTkey                            O(log|S|+|Sm|)
 getSortedListOfKeysGTkey                            O(log|S|+|Sm|)

 OVERVIEW:
 Height balanced tree, made of nodes -> TAVLTreeNode<TKey> forming a binary tree.
 Each node has a pointer to parent, left and right nodes, also a pointer to the key
 it holds. The upper node is the root whose parent is nil, walking down the tree we
 reach the leaves that have no child (i.e. left = right = nil). Additionally the
 height of each node is stored which is the longest distance from the node to nil
 walking down its subtree.

 After an insert/remove/extract ... queries BST balance is checked causing a number
 of left/right rotations on the sequence of parents of the inserted/deleted node up
 to the root which keeps the invariant : abs(left.height - right.height) < 2) for every
 node of the tree. BalanceValidation conditiondal define verifies at every new query
 that all the tree nodes are balance (which slows down the performance). any inbalanced
 node is reported with a message.

 COMMENTS:
 The nodes contain pointers to the keys (TKey) living the container C. If the class requires
 freeing, that should be done when the container is freed, not before the AVLTree is freed.
 Also the OutputSortedListOfKeys is a pointer to an internal field of TAVLTree<TKey> which
 is freed in TAVLTree<TKey>.free

 Note that some of the methods such as insert or extract require an input node (TAVLTreeNode<TKey>)
 which requires the user to create the nodes before using the methods. I find this
 convenient in situations where a member of the tree is extracted so its key can be modified and
 then reinserted in the tree, with these methds we can avoid unnecessary create/free of nodes.
 (see HowToUseExample.pas) }

{.$DEFINE BalanceValidation}  // for checking balance of the tree, KEEP IT SWITCH OFF for fast queries.

interface

uses Math, System.SysUtils, System.Variants, System.Classes, System.Generics.collections,
     Generics.Defaults;

type TsortingDirection = (ascend,descend);

type  TAVLTreeNode<TKey> = class

    parent, left, right : TAVLTreeNode<TKey>;
    key                 : TKey;
    compare             : TComparison<TKey>;

    keyString           : function(const key : Tkey): String;

    public
    procedure initNode(const key: Tkey; const compare : TComparison<Tkey>;
                       const parent: TAVLTreeNode<TKey>);
    procedure __str__(var StringList : TStringList);

    function find(const key : TKey) : TAVLTreeNode<TKey>;
    function find_min : TAVLTreeNode<TKey>;
    function find_max : TAVLTreeNode<TKey>;
    function successor : TAVLTreeNode<TKey>;
    function predecessor : TAVLTreeNode<TKey>;
    function insert(var node : TAVLTreeNode<TKey>) : Boolean;
    function delete : TAVLTreeNode<TKey>;
    procedure inOrderTraversalAscend(var sortedList : TList<TKey>);
    procedure inOrderTraversalDescend(var sortedList : TList<TKey>);

    private
    height              : Integer;
    procedure center(const FinalLength: Integer; const marker : char; var AString : String);
    procedure checkRI;
    function GetHeight : Integer;
    procedure update_height;
    procedure _str(var StringList : TStringList; var position, width : Integer);
end;


type TAVLTree<TKey> = Class(TObject)

    compare : TComparison<TKey>;
    private
    root                   : TAVLTreeNode<TKey>;
    FCount                 : Integer; // number of nodes in the tree
    OutputSortedListOfKeys : TList<TKey>;
    procedure checkRI;
    procedure left_rotate(const x : TAVLTreeNode<TKey>);
    procedure right_rotate(const x : TAVLTreeNode<TKey>);
    procedure rebalance(node: TAVLTreeNode<TKey>);
    function isBalanced(const node : TAVLTreeNode<TKey>) : Boolean;
    procedure extract(var node : TAVLTreeNode<TKey>); overload;
    function InsertInitiallizedNode(var node : TAVLTreeNode<TKey>) : Boolean;


    public
    constructor create(const compare_ : TComparison<TKey>);
    procedure Clear;
    procedure free;
    function insert(var node : TAVLTreeNode<TKey>) : Boolean; overload;
    function insert(const key : TKey) : Boolean; overload;
    function extract(const key : TKey) : TAVLTreeNode<TKey>; overload;
    function extract_min : TAVLTreeNode<TKey>;
    function extract_max : TAVLTreeNode<TKey>;
    function remove(const key : TKey) : Boolean;
    function find_min : TAVLTreeNode<TKey>;
    function find_max : TAVLTreeNode<TKey>;
    function find(const key : TKey): TAVLTreeNode<TKey>;
    property Count : integer read FCount;
    function successor(const key : TKey) : TAVLTreeNode<TKey>;
    function predecessor(const key : TKey) : TAVLTreeNode<TKey>;
    procedure swap(const key1, key2 : TKey);
    procedure __str__(var StringList : TStringList);
    function getSortedListOfKeys(dir : TsortingDirection = ascend) : TList<TKey>;
    function getSortedListOfKeysLTkey(const probe : TKey; dir : TsortingDirection = ascend) : TList<TKey>;
    function getSortedListOfKeysGTkey(const probe : TKey; dir : TsortingDirection = ascend) : TList<TKey>;
end;

//// begin software declaration
//procedure HowToUseExample;
//// end software declaration

implementation

uses Dialogs;

// Begin define methods for TAVLTreeNode
procedure TAVLTreeNode<TKey>.initNode(const key: TKey; const compare : TComparison<Tkey>; const parent: TAVLTreeNode<TKey>);
begin
  Self.key     := key;
  Self.compare := compare;
  Self.right   := nil;
  Self.left    := nil;
  Self.parent  := parent;
end;

procedure TAVLTreeNode<TKey>.center(const FinalLength: Integer; const marker : char; var AString : String);
var Dif, Difo2 : Integer;
begin
  Dif   := FinalLength - Astring.Length;
  Difo2 := Trunc(0.5*Dif);
  if Dif mod 2 = 0 then
   AString := ASTring.PadLeft(Astring.Length+Difo2,marker)
  else
   AString := ASTring.PadLeft(Astring.Length+Difo2+1,marker);
   AString := ASTring.PadRight(Astring.Length+Difo2,marker);
end;

procedure TAVLTreeNode<TKey>._str(var StringList : TStringList; var position, width : Integer);
(* Internal method for ASCII art *)
var AString                     : String;
    left_lines, right_lines     : TStringList;
    left_pos, left_width,
    right_pos, right_width,
    middle, i                   : Integer;
begin
  AString := self.keyString(self.key);

  left_lines := TStringList.Create;
  if NOT Assigned(self.left) then
  begin
    left_pos   := 0;
    left_width := 0;
  end
  else
    Self.left._str(left_lines,left_pos,left_width);

  right_lines := TStringList.Create;
  if NOT Assigned(self.right) then
  begin
    right_pos   := 0;
    right_width := 0;
  end
  else
    Self.right._str(right_lines,right_pos,right_width);

  middle   := max(right_pos + left_width - left_pos + 1, max(AString.Length, 2));
  position := Trunc((left_pos + middle)/2);
  width    := left_pos + middle + right_width - right_pos;

  while left_lines.Count < right_lines.Count do
    left_lines.Add(StringOfChar(' ',left_width));
  while right_lines.Count < left_lines.Count do
    right_lines.Add(StringOfChar(' ',right_width));
  if ((middle - AString.Length) mod 2 = 1) AND Assigned(Self.parent) AND
      (Self = self.parent.left) AND (AString.Length < middle) then
    AString := AString + '.';

  center(middle,'.',AString);
  if Astring[1] = '.'              then
    Astring := ' ' + AString.Substring(1,AString.Length-1);
  if Astring[Astring.Length] = '.' then
    Astring := AString.Substring(0,AString.Length-1) + ' ';

  StringList.Add(StringOfChar(' ',left_pos) + AString + StringOfChar(' ',right_width-right_pos));
  StringList.Add(StringOfChar(' ',left_pos) + '/' + StringOfChar(' ',middle-2) +
                              '\\' + StringOfChar(' ',right_width-right_pos));
  for i := 0 to left_lines.Count-1 do
    StringList.Add(left_lines[i] + StringOfChar(' ',width-left_width-right_width) + right_lines[i]);

  // Free memory
  left_lines.Free;
  right_lines.Free;
end;

procedure TAVLTreeNode<TKey>.__str__(var StringList : TStringList);
var zero : Integer;
begin
  zero := 0;
  self._str(StringList,zero,zero);
end;

function TAVLTreeNode<TKey>.find(const key : TKey) : TAVLTreeNode<TKey>;
(* returns the node containing the key in calling Node's subtree or nil if not found *)
var anInteger : Integer;
begin
  anInteger := Self.Compare(Self.key,key);
  if anInteger = 0 then
  begin
    RESULT := Self;
    Exit;
  end
  else if anInteger >0 then
  begin  // look for key in left subtree
    if NOT Assigned(Self.left) then
     begin RESULT := nil; Exit; end;
     RESULT := Self.left.find(key);
  end
  else  //then key > RESULT.key
  begin  // look for key in right subtree
    if NOT Assigned(Self.right) then
    begin  RESULT := nil; Exit; end;
    RESULT := Self.right.find(key);
  end;
end;

function TAVLTreeNode<TKey>.find_min : TAVLTreeNode<TKey>;
begin
  RESULT := Self;
  while Assigned(RESULT.left) do
    RESULT := RESULT.left;
end;

function TAVLTreeNode<TKey>.find_max : TAVLTreeNode<TKey>;
begin
  RESULT := Self;
  while Assigned(RESULT.right) do
    RESULT := RESULT.right;
end;

function TAVLTreeNode<TKey>.successor : TAVLTreeNode<TKey>;
(* Returns the node with the smallest key larger than calling node key,
   or nill if there is no larger key *)
begin
  if Assigned(self.right) then
  begin RESULT := self.right.find_min; Exit; end;

  RESULT := self;
  while (Assigned(RESULT.parent)) AND (RESULT.parent.right = RESULT) do
    RESULT := RESULT.parent;
  RESULT := RESULT.parent;
end;

function TAVLTreeNode<TKey>.predecessor : TAVLTreeNode<TKey>;
(* Returns the node with the largest key lower than calling node key,
   or nill if there in no lower key *)
begin
  if Assigned(self.left) then
  begin RESULT := self.left.find_max; Exit; end;

  RESULT := self;
  while (Assigned(RESULT.parent)) AND (RESULT.parent.left = RESULT) do
    RESULT := RESULT.parent;
  RESULT := RESULT.parent;
end;

function TAVLTreeNode<TKey>.insert(var node : TAVLTreeNode<TKey>) : Boolean;
(* inserts input node into the subtree rooted as calling node, returns FALSE
   if the nodes key is already in the Tree *)
var aInteger : Integer;
begin
  if NOT Assigned(node) then
  begin RESULT := FALSE;  Exit; end;

  aInteger := Self.Compare(Self.key,node.key);

  if aInteger = 1 then
  begin
    if NOT Assigned(self.left) then
    begin
      node.parent := self;
      self.left   := node;
    end
    else  self.left.insert(node);
    RESULT := TRUE;
  end
  else if aInteger = -1 then
  begin
    if NOT Assigned(self.right) then
    begin
      node.parent := self;
      self.right  := node;
    end
    else  self.right.insert(node);
    RESULT := TRUE;
  end
  else // then key1 = key2 and and insert fails
    RESULT := FALSE;
end;

function TAVLTreeNode<TKey>.delete : TAVLTreeNode<TKey>;
(* deletes and returns calling node from tree, assumed calling node is not the root *)
var next : TAVLTreeNode<TKey>;
begin

  if (NOT Assigned(self.left)) OR (NOT Assigned(self.right)) then
  begin
    if self = self.parent.left then
    begin
      if Assigned(self.left) then
      begin
        self.parent.left := self.left;
        self.left.parent := self.parent;
      end
      else if Assigned(self.right) then
      begin
        self.parent.left  := self.right;
        self.right.parent := self.parent;
      end
      else // deleted node is a leaf
        self.parent.left := nil;
    end
    else
    begin
      if Assigned(self.left) then
      begin
        self.parent.right := self.left;
        self.left.parent  := self.parent;
      end
      else if Assigned(self.right) then
      begin
        self.parent.right := self.right;
        self.right.parent := self.parent;
      end
      else // deleted node is a leaf
        self.parent.right := nil;
    end;
    RESULT := self;
  end
  else  // deleted node has left and right childs
  begin
    next := self.successor; // cannot be nil
    self.key := next.key;
    RESULT := next.delete;
  end;
end;

procedure TAVLTreeNode<TKey>.checkRI;
(* Checks the BST representation invariant around this node,
   Raises an exception if the RI is violated *)
begin
  if Assigned(self.left) then
  begin
    if self.left.Compare(Self.left.key,self.key) = 1 then
      Raise Exception.Create('BST RI violated by a left node key');
    if self.left.parent <> self then
      Raise Exception.Create('BST RI violated by a left node parent');

    self.left.checkRI;
  end;
  if Assigned(self.right) then
  begin
    if self.right.Compare(Self.right.key,self.key) = -1 then
      Raise Exception.Create('BST RI violated by a right node key');
    if self.right.parent <> self then
      Raise Exception.Create('BST RI violated by a right node parent');

    self.right.checkRI;
  end;
end;

function TAVLTreeNode<TKey>.GetHeight : Integer;
begin
  if NOT Assigned(Self) then
    RESULT := -1
  else
    RESULT := Self.height;
end;

procedure TAVLTreeNode<TKey>.update_height;
begin
  Self.height := max(Self.left.getHeight, Self.right.getHeight) + 1
end;

procedure TAVLTreeNode<TKey>.inOrderTraversalAscend(var sortedList : TList<TKey>);
begin
  if Assigned(Self) then
  begin
    self.left.inOrderTraversalAscend(sortedList);
    sortedList.Add(self.key);
    self.right.inOrderTraversalAscend(sortedList);
  end;
end;

procedure TAVLTreeNode<TKey>.inOrderTraversalDescend(var sortedList : TList<TKey>);
begin
  if Assigned(Self) then
  begin
    self.right.inOrderTraversalDescend(sortedList);
    sortedList.Add(self.key);
    self.left.inOrderTraversalDescend(sortedList);
  end;
end;
// End define methods for TAVLTreeNode

// Begin define methods for TAVLTree
constructor TAVLTree<TKey>.create(const compare_ : TComparison<TKey>);
begin
  inherited create;
  FCount                 := 0;
  root                   := nil;
  compare                := compare_;
  OutputSortedListOfKeys := TList<TKey>.create;
end;

procedure TAVLTree<TKey>.Clear;
var node : TAVLTreeNode<TKey>;
begin
  while Assigned(Self.root) do
    Self.remove(self.root.key);
  FCount := 0;
  OutputSortedListOfKeys.Clear;
end;

procedure TAVLTree<TKey>.free;
begin
  Clear;
  OutputSortedListOfKeys.Free;
  inherited free;
end;

procedure TAVLTree<TKey>.__str__(var StringList : TStringList);
begin
  if NOT Assigned(self.root) then
    StringList.Add('<empty tree>')
  else
    self.root.__str__(StringList);
end;

function TAVLTree<TKey>.find(const key : TKey) : TAVLTreeNode<TKey>;
(* returns node containing key or nil if it is not there *)
begin
  RESULT := Self.root.find(key);
end;

function TAVLTree<TKey>.find_min : TAVLTreeNode<TKey>;
(* returns node with lowest key or nil if there are no nodes in the Tree *)
begin
  RESULT := Self.root.find_min;
end;

function TAVLTree<TKey>.find_max : TAVLTreeNode<TKey>;
(* returns node with largest key or nil if there are no nodes in the Tree *)
begin
  RESULT := Self.root.find_max;
end;

function TAVLTree<TKey>.insert(const key : TKey) : Boolean;
var node : TAVLTreeNode<TKey>;
begin
  node := TAVLTreeNode<TKey>.create;
  node.initNode(key,compare,nil);
  RESULT := InsertInitiallizedNode(node);
end;

function TAVLTree<TKey>.insert(var node : TAVLTreeNode<TKey>) : Boolean;
(* Insert node in the BST, returns False if insertion fails because the key is
   already in the tree. Input node needs to be created and hold a valid key *)
begin
  // SAVEGUARD: ensures node is initiallized
  node.initNode(node.key,compare,nil);
  RESULT := InsertInitiallizedNode(node);
end;

function TAVLTree<TKey>.InsertInitiallizedNode(var node : TAVLTreeNode<TKey>) : Boolean;
(* private methosd to be called by insert fuunctions *)
begin
  if NOT Assigned(self.root) then // First Node in the tree
  begin RESULT := TRUE;  self.root := node;  end
  else
  begin RESULT := self.root.insert(node); end;

  Self.rebalance(node);
  Inc(FCount);

  {$IFDEF BalanceValidation}
  Self.checkRI;  // compare function needs to be defined at this point
  if NOT Self.isBalanced(self.root) then
    Raise Exception.Create('AVLTree Error : inbalance detected');
  {$ENDIF}
end;

function TAVLTree<TKey>.remove(const key : TKey) : Boolean;
{ * Extracts and frees the tree node holding key, if it is not in the trre returns FALSE * }
var node : TAVLTreeNode<TKey>;
begin
  node := extract(key);
  if Assigned(node) then
  begin
    RESULT := TRUE;
    node.Free;
  end
  else  RESULT := FALSE;
end;

procedure TAVLTree<TKey>.extract(var node : TAVLTreeNode<TKey>);
{extract existing node from BST}
var pseudoroot, deleted : TAVLTreeNode<TKey>;
begin
  if NOT Assigned(node.parent) then  // node = root
  begin
    pseudoroot := TAVLTreeNode<TKey>.Create;
    pseudoroot.initNode(node.key,self.compare,nil);
    pseudoroot.left  := self.root;
    self.root.parent := pseudoroot;
    node             := self.root.delete;
    self.root        := pseudoroot.left;

    if Assigned(self.root) then
      self.root.parent := nil;

    Self.rebalance(node.parent);
    pseudoroot.Free;
  end
  else
  begin
    node := node.delete;
    Self.rebalance(node.parent);
  end;
  Dec(FCount);

  {$IFDEF BalanceValidation}
  Self.checkRI;
  if NOT Self.isBalanced(self.root) then
    Raise Exception.Create('AVLTree inbalance detected');
  {$ENDIF}
end;

function TAVLTree<TKey>.extract(const key : TKey) : TAVLTreeNode<TKey>;
(* extracts from the BST and returns the node with the given key if it exists
   in the BST otherwise nil is output *)
begin
  RESULT := self.root.find(key);
  if Assigned(RESULT) then
    extract(RESULT);
end;

function TAVLTree<TKey>.extract_min : TAVLTreeNode<TKey>;
(* extracts from the BST and returns the node with lowest key, nil if empty Tree *)
begin
  if Assigned(root) then
  begin
    RESULT := root.find_min;
    extract(RESULT);
  end
  else  RESULT := nil;
end;

function TAVLTree<TKey>.extract_max : TAVLTreeNode<TKey>;
(* extracts from the BST and returns the node with largest key, nil if empty Tree *)
begin
  if Assigned(root) then
  begin
    RESULT := root.find_max;
    extract(RESULT);
  end
  else  RESULT := nil;
end;

function TAVLTree<TKey>.successor(const key : TKey) : TAVLTreeNode<TKey>;
(* Returns the node that contains the successor (next larger) key in the BST
   or nil if key is the largest key. If the key is not in the tree succ=nil aswell *)
begin
  RESULT := self.find(key);
  if Assigned(RESULT) then
    RESULT := RESULT.successor;
end;

function TAVLTree<TKey>.predecessor(const key : TKey) : TAVLTreeNode<TKey>;
(* Returns the node that contains the predecessor (previous larger) key in the BST
   or nil if key is the lowest key. If the key is not in the tree succ=nil aswell *)
begin
  RESULT := self.find(key);
  if Assigned(RESULT) then
    RESULT := RESULT.predecessor;
end;

procedure TAVLTree<TKey>.swap(const key1, key2 : TKey);
{ be aware this might cause the tree to be incoherent}
var node1, node2 : TAVLTreeNode<TKey>;
begin
  node1 := find(key1);
  node2 := find(key2);

  node1.key  := key2;
  node2.key  := key1;
end;

function TAVLTree<TKey>.getSortedListOfKeys(dir : TsortingDirection = ascend) : TList<TKey>;
{ outputs a list with all keys int the AVLTree in ascending/descending order.
  OutPutListOfKeys is freed in TAVLTree<TKey>.free }
begin
  RESULT := OutputSortedListOfKeys;
  RESULT.Clear;
  if dir = ascend then
    root.inOrderTraversalAscend(RESULT)
  else
    root.inOrderTraversalDescend(RESULT);
end;

function TAVLTree<TKey>.getSortedListOfKeysLTkey(const probe : TKey; dir : TsortingDirection = ascend): TList<TKey>;
{ outputs a list with all keys int the AVLTree < inputKey, in ascending/descending order.
  OutPutListOfKeys is freed in TAVLTree<TKey>.free }
var node        : TAVLTreeNode<TKey>;
    ListOfNodes : TKey;
    aInteger    : Integer;
begin
  RESULT := OutputSortedListOfKeys;
  RESULT.Clear;
  if Assigned(root) then
  begin
    node := root;

    while Assigned(node) do
    begin
      aInteger := node.compare(node.key,probe);

      if aInteger = -1 then node := node.left
      else
      begin
        node.left.inOrderTraversalAscend(RESULT);
        RESULT.Add(node.key);
        node := node.right;
      end;
    end;

    if dir = descend then RESULT.Reverse;
  end;
end;

function TAVLTree<TKey>.getSortedListOfKeysGTkey(const probe : TKey; dir : TsortingDirection = ascend): TList<TKey>;
{ outputs a list with all keys int the AVLTree > inputKey, in ascending/descending order.
  OutPutListOfKeys is freed in TAVLTree<TKey>.free }
var node        : TAVLTreeNode<TKey>;
    ListOfNodes : TKey;
    aInteger    : Integer;
begin
  RESULT := OutputSortedListOfKeys;
  RESULT.Clear;
  if Assigned(root) then
  begin
    node := root;

    while Assigned(node) do
    begin
      aInteger := node.compare(node.key,probe);

      if aInteger = -1 then node := node.right
      else
      begin
        node.right.inOrderTraversalDescend(RESULT);
        RESULT.Add(node.key);
        node := node.left;
      end;
    end;

    if dir = Ascend then RESULT.Reverse;
  end;
end;

procedure TAVLTree<TKey>.checkRI;
(* Checks the BST representation invariant. Raises an exception if RI is violated *)
begin
  if Assigned(self.root) then
  begin
    if Assigned(self.root.parent) then
      Raise Exception.Create('BST RI violated by root node parent');
    self.root.checkRI;
  end;
end;

procedure TAVLTree<TKey>.left_rotate(const x : TAVLTreeNode<TKey>);
var y : TAVLTreeNode<TKey>;
begin
  y        := x.right;
  y.parent := x.parent;
  if NOT Assigned(y.parent) then
    self.root := y
  else
  begin
    if x = y.parent.left then
      y.parent.left := y
    else if x = y.parent.right then
      y.parent.right := y;
  end;

  x.right := y.left;
  if Assigned(x.right) then
    x.right.parent := x;

  y.left   := x;
  x.parent := y;
  x.update_height;
  y.update_height;
end;

procedure TAVLTree<TKey>.right_rotate(const x : TAVLTreeNode<TKey>);
var y : TAVLTreeNode<TKey>;
begin
  y        := x.left;
  y.parent := x.parent;
  if NOT Assigned(y.parent) then
    self.root := y
  else
  begin
    if y.parent.left = x then
      y.parent.left := y
    else if y.parent.right = x then
      y.parent.right := y;
  end;

  x.left := y.right;
  if Assigned(x.left) then
    x.left.parent := x;
  y.right := x;
  x.parent := y;
  x.update_height;
  y.update_height;
end;

procedure TAVLTree<TKey>.rebalance(node: TAVLTreeNode<TKey>);
var leftH, rightH : Integer;
begin
  while Assigned(node) do
  begin
    node.update_height;
    leftH  := node.left.GetHeight;
    rightH := node.right.GetHeight;
    if leftH >= (2 + rightH) then       // left inbalance
    begin
      if node.left.left.GetHeight >= node.left.right.GetHeight then
        self.right_rotate(node)
      else
      begin
        self.left_rotate(node.left);
        self.right_rotate(node);
      end;
    end
    else if rightH >= (2 + leftH) then  // right inbalance
    begin
      if node.right.right.GetHeight >= node.right.left.GetHeight then
        self.left_rotate(node)
      else
      begin
        self.right_rotate(node.right);
        self.left_rotate(node);
      end;
    end;
    node := node.parent;
  end;
end;

function TAVLTree<TKey>.isBalanced(const node : TAVLTreeNode<TKey>) : Boolean;
begin
  if NOT Assigned(node) then
    RESULT := TRUE
  else if abs(node.right.GetHeight - node.left.GetHeight) >= 2 then
    RESULT := FALSE
  else
    RESULT := Self.isBalanced(node.left) AND Self.isBalanced(node.right);
end;
// End define methods for TAVLTree


// HOW TO USE EXAMPLE
{  Tkey is the TMoneyBag class. Every bag has a number of coins that we can reduce
   or increasre by taking or inserting coins in the bag. The example illustrates
   the usage of TAVLTree<TKey> class.}

type TMoneyBag = class
  coinsNo : Integer;
  bagTag  : Integer;

  constructor create(const coinNo_,bagTag_ : Integer);
  function takeCoins(const coins : Integer) : Boolean;
  procedure InsertCoins(const coins : Integer);
end;

// begin define methods of TMoneyBag
constructor TMoneyBag.create(const coinNo_,bagTag_ : Integer);
begin
  inherited create;
  coinsNo := coinNo_;
  bagTag  := bagTag_;
end;

function TMoneyBag.takeCoins(const coins : Integer) : Boolean;
begin
  if coins > coinsNo then RESULT := FALSE
  else
  begin
    Dec(coinsNo,coins);
    RESULT := TRUE;
  end;
end;

procedure TMoneyBag.InsertCoins(const coins : Integer);
begin
  Inc(coinsNo,coins);
end;
// end define metods of TMoneyBag

// define relational operator using number of coins in the bag
function compareMoneyBags(const left, right: TMoneyBag) : Integer;
begin
  RESULT := TComparer<Single>.Default.Compare(left.coinsNo,right.coinsNo);
  if RESULT = 0 then
    RESULT := TComparer<Integer>.Default.Compare(left.bagTag,right.bagTag);
end;

procedure HowToUseExample;
var C, SL            : TList<TmoneyBag>;
    BST              : TAVLTree<TMoneyBag>;
    i, Nbags, price,
    FInalCount       : Integer;
    bag, fakeBag     : TMoneyBag;
    node1, node2     : TAVLTreeNode<TMoneyBag>;
begin
  // create a List with 100 bags with random number of coins in [0,20]
  C     := TList<TMoneyBag>.create;
  Nbags := 100;
  for i := 0 to Nbags-1 do
  begin
    bag := TMoneyBag.create(round(random*20),i);
    C.Add(bag);
  end;

  // construct and build AVLTree
  BST := TAVLTree<TMoneyBag>.create(compareMoneyBags);
  for i := 0 to C.Count -1 do
  begin
    bag := C[i];
    BST.insert(bag);   // node is created inside this insert overload
  end;

  // now in the tree we have too many bags with few coins each. so we want to
  // take the money in just 20 bags keeping them all more or less full
  while BST.Count > 21 do
  begin
    node1 := BST.extract_min;
    node2 := BST.extract_min;
    node2.key.InsertCoins(node1.key.coinsNo);
    node1.Free;
    BST.insert(node2);  // this insert overload requires a previously created node with a valid key
  end;
  // now we just spend money from the biggest bag until all bags have less than 10 coins
  node1 := BST.extract_max;
  while node1.key.coinsNo > 9 do
  begin
    price := round(random*10);
    while price <> 0 do
    begin
      if node1.key.takeCoins(price) then
      begin
        BST.insert(node1);
        price := 0;
      end
      else
      begin
        Dec(price,node1.key.coinsNo);
        node1.Free; // get rid of empty bags
      end;
      //update
      node1 := BST.extract_max;
    end;
  end;
  // reinsert last extracted bag
  BST.insert(node1);

  // at this point we get a sortedList of bags with more than 5 coins creating
  // the appropriate key for searching the tree
  fakeBag := TMoneyBag.create(6,-1); // so any bag in C with 6 coins will be > than fakeBag
  SL      := BST.getSortedListOfKeysGTkey(fakeBag,descend);
  fakeBag.Free;

  // we want to put the money in SL subset in a single bag. Nodes are extracted from the tree
  // so their keys can be used before the node is freed
  node1 := BST.extract(SL[0]);
  for i := 1 to SL.Count-1 do
  begin
    node2 := BST.extract(SL[i]);
    node1.key.InsertCoins(node2.key.coinsNo);
    node2.Free;
  end;
  BST.insert(node1);

  // know count the money left and free the tree
  FinalCount := 0;
  while BST.Count > 0 do
  begin
    node1 := BST.extract_max;
    Inc(FInalCount,node1.key.coinsNo);
    node1.Free;
  end;
  BST.free;

  // Free memory
  for i := 0 to C.Count-1 do
    C[i].Free; // Tkey class freed here
  C.Free;
end;


end.
