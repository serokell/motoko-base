/// Stable ordered set implemented as a red-black tree. Currently built on top of PersistentOrderedMap by storing () values.
///
/// Performance:
/// * Runtime: `O(log(n))` worst case cost per insertion, removal, and retrieval operation.
/// * Space: `O(n)` for storing the entire tree.
/// `n` denotes the number of elements (i.e. nodes) stored in the tree.
///
/// The set operations implementation is derived from:
/// Tobias Nipkow's "Functional Data Structures and Algorithms", 10: 117-125 (2024).


import Map "PersistentOrderedMap";
import I "Iter";
import Nat "Nat";
import O "Order";
import Option "Option";

module {
  public type Set<T> = Map.Map<T,()>;

  /// Opertaions on `Set`, that require a comparator.
  ///
  /// The object should be created once, then used for all the operations
  /// with `Set` to maintain invariant that comparator did not changed.
  ///
  /// `SetOps` contains methods that require `compare` internally:
  /// operations that may reshape a `Set` or should find something.
  public class SetOps<T>(compare : (T, T) -> O.Order) {
    let mapOps = Map.MapOps<T>(compare);

    /// Returns a new Set, containing all entries given by the iterator `i`.
    /// If there are multiple identical entries only one is taken.
    ///
    /// Example:
    /// ```motoko
    /// import Set "mo:base/PersistentOrderedSet";
    /// import Nat "mo:base/Nat"
    /// import Iter "mo:base/Iter"
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set = setOps.fromIter(Iter.fromArray([0, 2, 1]));
    ///
    /// Debug.print(debug_show(Iter.toArray(Set.elements(set))));
    ///
    /// // [0, 1, 2]
    /// ```
    ///
    /// Runtime: `O(n * log(n))`.
    /// Space: `O(n)` retained memory plus garbage, see the note below.
    /// where `n` denotes the number of elements stored in the set and
    /// assuming that the `compare` function implements an `O(1)` comparison.
    ///
    /// Note: Creates `O(n * log(n))` temporary objects that will be collected as garbage.
    public func fromIter(i : I.Iter<T>) : Set<T> {
      var set = #leaf : Set<T>;
      for(val in i) {
        set := put(set, val);
      };
      set
    };

    /// Insert the value `value` into the set `s`. Has no effect if `value` is already
    /// present in the set. Returns a modified set.
    ///
    /// Example:
    /// ```motoko
    /// import Set "mo:base/PersistentOrderedSet";
    /// import Nat "mo:base/Nat"
    /// import Iter "mo:base/Iter"
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// var set = Set.empty<Nat>();
    ///
    /// set := setOps.put(set, 0);
    /// set := setOps.put(set, 2);
    /// set := setOps.put(set, 1);
    ///
    /// Debug.print(debug_show(Iter.toArray(Set.elements(set))));
    ///
    /// // [0, 1, 2]
    /// ```
    ///
    /// Runtime: `O(log(n))`.
    /// Space: `O(1)` retained memory plus garbage, see the note below.
    /// where `n` denotes the number of key-value entries stored in the set and
    /// assuming that the `compare` function implements an `O(1)` comparison.
    ///
    /// Note: Creates `O(log(n))` temporary objects that will be collected as garbage.
    public func put(s : Set<T>, value : T) : Set<T> = mapOps.put<()>(s, value, ());

    /// Deletes the value `value` from the set `s`. Has no effect if `value` is not
    /// present in the set. Returns modified set.
    ///
    /// Example:
    /// ```motoko
    /// import Set "mo:base/PersistentOrderedSet";
    /// import Nat "mo:base/Nat"
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set = setOps.fromIter(Iter.fromArray([0, 2, 1]));
    ///
    /// Debug.print(debug_show(Iter.toArray(Set.elements(setOps.delete(set, 1)))));
    /// Debug.print(debug_show(Iter.toArray(Set.elements(setOps.delete(set, 42)))));
    ///
    /// // [0, 2]
    /// // [0, 1, 2]
    /// ```
    ///
    /// Runtime: `O(log(n))`.
    /// Space: `O(1)` retained memory plus garbage, see the note below.
    /// where `n` denotes the number of elements stored in the set and
    /// assuming that the `compare` function implements an `O(1)` comparison.
    ///
    /// Note: Creates `O(log(n))` temporary objects that will be collected as garbage.
    public func delete(s : Set<T>, value : T) : Set<T> = mapOps.delete<()>(s, value);

    /// Test if the set 's' contains a given element.
    ///
    /// Example:
    /// ```motoko
    /// import Set "mo:base/PersistentOrderedSet";
    /// import Nat "mo:base/Nat"
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set = setOps.fromIter(Iter.fromArray([0, 2, 1]));
    ///
    /// Debug.print(debug_show setOps.contains(set, 1));
    /// Debug.print(debug_show setOps.contains(set, 42));
    ///
    /// // true
    /// // false
    /// ```
    ///
    /// Runtime: `O(log(n))`.
    /// Space: `O(1)` retained memory plus garbage, see the note below.
    /// where `n` denotes the number of elements stored in the set and
    /// assuming that the `compare` function implements an `O(1)` comparison.
    ///
    /// Note: Creates `O(log(n))` temporary objects that will be collected as garbage.
    public func contains(s : Set<T>, value : T) : Bool = Option.isSome(mapOps.get(s, value));

    /// [Set union](https://en.wikipedia.org/wiki/Union_(set_theory)) operation.
    ///
    /// Example:
    /// ```motoko
    /// import Set "mo:base/PersistentOrderedSet";
    /// import Nat "mo:base/Nat";
    /// import Iter "mo:base/Iter"
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set1 = setOps.fromIter(Iter.fromArray([0, 1, 2]));
    /// let set2 = setOps.fromIter(Iter.fromArray([2, 3, 4]));
    ///
    /// Debug.print(debug_show Iter.toArray(Set.elements(setOps.union(set1, set2))));
    ///
    /// // [0, 1, 2, 3, 4]
    /// ```
    ///
    /// Runtime: `O(m * log(n/m + 1))`.
    /// Space: `O(m * log(n/m + 1))`, where `m` and `n` denote the number of elements
    /// in the sets, and `m <= n`.
    public func union(s1 : Set<T>, s2 : Set<T>) : Set<T> {
      switch (s1, s2) {
        case (#leaf, set) { set };
        case (set, #leaf) { set };
        case (#node (_,l1, (k, v), r1), _) {
          let (l2, _, r2) = Map.Internal.split(k, s2, compare);
          Map.Internal.join(union(l1, l2), (k, v), union(r1, r2))
        };
      };
    };

    /// [Set intersection](https://en.wikipedia.org/wiki/Intersection_(set_theory)) operation.
    ///
    /// Example:
    /// ```motoko
    /// import Set "mo:base/PersistentOrderedSet";
    /// import Nat "mo:base/Nat";
    /// import Iter "mo:base/Iter";
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set1 = setOps.fromIter(Iter.fromArray([0, 1, 2]));
    /// let set2 = setOps.fromIter(Iter.fromArray([1, 2, 3]));
    ///
    /// Debug.print(debug_show Iter.toArray(Set.elements(setOps.intersect(set1, set2))));
    ///
    /// // [1, 2]
    /// ```
    ///
    /// Runtime: `O(m * log(n/m + 1))`.
    /// Space: `O(m * log(n/m + 1))`, where `m` and `n` denote the number of elements
    /// in the sets, and `m <= n`.
    public func intersect(s1 : Set<T>, s2 : Set<T>) : Set<T> {
      switch (s1, s2) {
        case (#leaf, _) { #leaf };
        case (_, #leaf) { #leaf };
        case (#node (_, l1, (k, v), r1), _) {
          let (l2, b2, r2) = Map.Internal.split(k, s2, compare);
          let l = intersect(l1, l2);
          let r = intersect(r1, r2);
          if b2 { Map.Internal.join (l, (k, v), r) }
          else { Map.Internal.join2(l, r) };
        };
      };
    };

    /// [Set difference](https://en.wikipedia.org/wiki/Difference_(set_theory)).
    ///
    /// Example:
    /// ```motoko
    /// import Set "mo:base/PersistentOrderedSet";
    /// import Nat "mo:base/Nat";
    /// import Iter "mo:base/Iter"
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set1 = setOps.fromIter(Iter.fromArray([0, 1, 2]));
    /// let set2 = setOps.fromIter(Iter.fromArray([1, 2, 3]));
    ///
    /// Debug.print(debug_show Iter.toArray(Set.elements(setOps.diff(set1, set2))));
    ///
    /// // [0]
    /// ```
    ///
    /// Runtime: `O(m * log(n/m + 1))`.
    /// Space: `O(m * log(n/m + 1))`, where `m` and `n` denote the number of elements
    /// in the sets, and `m <= n`.
    public func diff(s1 : Set<T>, s2 : Set<T>) : Set<T> {
      switch (s1, s2) {
        case (#leaf, _) { #leaf };
        case (set, #leaf) { set };
        case (_, (#node(_, l2, (k, _), r2))) {
          let (l1, _, r1) = Map.Internal.split(k, s1, compare);
          Map.Internal.join2(diff(l1, l2), diff(r1, r2));
        }
      }
    };

    /// Creates a new `Set` by applying `f` to each entry in the set `s`. Each element
    /// `x` in the old set is transformed into a new entry `x2`, where
    /// the new value `x2` is created by applying `f` to `x`.
    /// The result set may be smaller than the original set due to duplicate elements.
    ///
    /// Example:
    /// ```motoko
    /// import Map "mo:base/PersistentOrderedMap";
    /// import Nat "mo:base/Nat"
    /// import Iter "mo:base/Iter"
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set = setOps.fromIter(Iter.fromArray([0, 1, 2, 3]));
    ///
    /// func f(x : Nat) : Nat = if (x < 2) { x } else { 0 };
    ///
    /// let resSet = setOps.map(set, f);
    ///
    /// Debug.print(debug_show(Iter.toArray(Set.elements(resSet))));
    /// // [0, 1]
    /// ```
    ///
    /// Cost of mapping all the elements:
    /// Runtime: `O(n)`.
    /// Space: `O(n)` retained memory
    /// where `n` denotes the number of elements stored in the set.
    public func map<T1>(s : Set<T1>, f : T1 -> T) : Set<T> = fromIter(I.map(elements(s), f));

    /// Creates a new map by applying `f` to each element in the set `s`. For each element
    /// `x` in the old set, if `f` evaluates to `null`, the element is discarded.
    /// Otherwise, the entry is transformed into a new entry `x2`, where
    /// the new value `x2` is the result of applying `f` to `x`.
    ///
    /// Example:
    /// ```motoko
    /// import Map "mo:base/PersistentOrderedMap";
    /// import Nat "mo:base/Nat"
    /// import Iter "mo:base/Iter";
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set = setOps.fromIter(Iter.fromArray([0, 1, 2, 3]));
    ///
    /// func f(x : Nat) : ?Nat {
    ///   if(x == 0) {null}
    ///   else { ?( x * 2 )}
    /// };
    ///
    /// let newRbSet = setOps.mapFilter(set, f);
    ///
    /// Debug.print(debug_show(Iter.toArray(Set.elements(newRbSet))));
    ///
    /// // [2, 4, 6]
    /// ```
    ///
    /// Runtime: `O(n)`.
    /// Space: `O(n)` retained memory plus garbage, see the note below.
    /// where `n` denotes the number of elements stored in the set and
    /// assuming that the `compare` function implements an `O(1)` comparison.
    ///
    /// Note: Creates `O(log(n))` temporary objects that will be collected as garbage.
    public func mapFilter<T1>(s: Set<T1>, f : T1 -> ?T) : Set<T> {
        var res = #leaf : Set<T>;
        for(x in elements(s)) {
          switch(f x){
            case null {};
            case (?x2) {
              res := put(res, x2);
            }
          }
        };
        res
    };

    /// Test if `set1` is subset of `set2`.
    ///
    /// Example:
    /// ```motoko
    /// import Set "mo:base/PersistentOrderedSet";
    /// import Nat "mo:base/Nat";
    /// import Iter "mo:base/Iter"
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set1 = setOps.fromIter(Iter.fromArray([1, 2]));
    /// let set2 = setOps.fromIter(Iter.fromArray([0, 2, 1]));
    ///
    /// Debug.print(debug_show setOps.isSubset(set1, set2));
    ///
    /// // true
    /// ```
    ///
    /// Runtime: `O(m * log(n))`.
    /// Space: `O(1)` retained memory plus garbage, see the note below.
    /// where `m` and `n` denote the number of elements stored in the sets set1 and set2, respectively,
    /// and assuming that the `compare` function implements an `O(1)` comparison.
    ///
    /// Note: Creates `O(m * log(n))` temporary objects that will be collected as garbage.
    public func isSubset(s1 : Set<T>, s2 : Set<T>) : Bool {
      if (size(s1) > size(s2)) { return false; };
      isSubsetHelper(s1, s2)
    };

    /// Test if two sets are equal.
    ///
    /// Example:
    /// ```motoko
    /// import Set "mo:base/PersistentOrderedSet";
    /// import Nat "mo:base/Nat";
    /// import Iter "mo:base/Iter"
    /// import Debug "mo:base/Debug";
    ///
    /// let setOps = Set.SetOps<Nat>(Nat.compare);
    /// let set1 = setOps.fromIter(Iter.fromArray([0, 2, 1]));
    /// let set2 = setOps.fromIter(Iter.fromArray([1, 2]));
    ///
    /// Debug.print(debug_show setOps.equals(set1, set1));
    /// Debug.print(debug_show setOps.equals(set1, set2));
    ///
    /// // true
    /// // false
    /// ```
    ///
    /// Runtime: `O(m * log(n))`.
    /// Space: `O(1)` retained memory plus garbage, see the note below.
    /// where `m` and `n` denote the number of elements stored in the sets set1 and set2, respectively,
    /// and assuming that the `compare` function implements an `O(1)` comparison.
    ///
    /// Note: Creates `O(m * log(n))` temporary objects that will be collected as garbage.
    public func equals (s1 : Set<T>, s2 : Set<T>) : Bool {
      if (size(s1) != size(s2)) { return false; };
      isSubsetHelper(s1, s2)
    };

    func isSubsetHelper(s1 : Set<T>, s2 : Set<T>) : Bool {
      for (x in elements(s1)) {
        if (not (contains(s2, x))) {
          return false;
        }
      };
      return true;
    };
  };

  /// Returns an Iterator (`Iter`) over the elements of the set.
  /// Iterator provides a single method `next()`, which returns
  /// elements in ascending order, or `null` when out of elements to iterate over.
  ///
  /// Example:
  /// ```motoko
  /// import Set "mo:base/PersistentOrderedSet";
  /// import Nat "mo:base/Nat"
  /// import Iter "mo:base/Iter"
  /// import Debug "mo:base/Debug";
  ///
  /// let setOps = Set.SetOps<Nat>(Nat.compare);
  /// let set = setOps.fromIter(Iter.fromArray([0, 2, 1]));
  ///
  /// Debug.print(debug_show(Iter.toArray(Set.elements(set))));
  ///
  /// // [0, 1, 2]
  /// ```
  /// Cost of iteration over all elements:
  /// Runtime: `O(n)`.
  /// Space: `O(log(n))` retained memory plus garbage, see the note below.
  /// where `n` denotes the number of elements stored in the set.
  ///
  /// Note: Full set iteration creates `O(n)` temporary objects that will be collected as garbage.
  public func elements<T>(s : Set<T>) : I.Iter<T> = Map.keys<T, ()>(s);

  /// Create a new empty Set.
  ///
  /// Example:
  /// ```motoko
  /// import Set "mo:base/PersistentOrderedSet";
  ///
  /// let set = Set.empty<Nat>();
  ///
  /// Debug.print(debug_show(Set.size(set)));
  ///
  /// // 0
  /// ```
  ///
  /// Cost of empty set creation
  /// Runtime: `O(1)`.
  /// Space: `O(1)`
  public func empty<T>() : Set<T> = Map.empty<T, ()>();

  /// Returns the number of elements in the set.
  ///
  /// Example:
  /// ```motoko
  /// import Set "mo:base/PersistentOrderedSet";
  /// import Nat "mo:base/Nat"
  /// import Iter "mo:base/Iter"
  /// import Debug "mo:base/Debug";
  ///
  /// let setOps = Set.SetOps<Nat>(Nat.compare);
  /// let set = setOps.fromIter(Iter.fromArray([0, 2, 1]));
  ///
  /// Debug.print(debug_show(Map.size(set)));
  ///
  /// // 3
  /// ```
  ///
  /// Runtime: `O(n)`.
  /// Space: `O(1)`.
  /// where `n` denotes the number of elements stored in the set.
  public func size<T>(s : Set<T>) : Nat = Map.size<T, ()>(s);

  /// Collapses the elements in `set` into a single value by starting with `base`
  /// and progessively combining elements into `base` with `combine`. Iteration runs
  /// left to right.
  ///
  /// Example:
  /// ```motoko
  /// import Set "mo:base/PersistentOrderedSet";
  /// import Nat "mo:base/Nat"
  /// import Iter "mo:base/Iter"
  /// import Debug "mo:base/Debug";
  ///
  /// let setOps = Set.SetOps<Nat>(Nat.compare);
  /// let set = setOps.fromIter(Iter.fromArray([0, 2, 1]));
  ///
  /// func folder(val : Nat, accum : Nat) : Nat = val + accum;
  ///
  /// Debug.print(debug_show(Set.foldLeft(set, 0, folder)));
  ///
  /// // 3
  /// ```
  ///
  /// Cost of iteration over all elements:
  /// Runtime: `O(n)`.
  /// Space: depends on `combine` function plus garbage, see the note below.
  /// where `n` denotes the number of elements stored in the set.
  ///
  /// Note: Full set iteration creates `O(n)` temporary objects that will be collected as garbage.
  public func foldLeft<T, Accum> (
    set : Set<T>,
    base : Accum,
    combine : (T, Accum) -> Accum
  ) : Accum
  {
    Map.foldLeft(
      set,
      base,
      func (x : T , _ : (), acc : Accum) : Accum { combine(x, acc) }
    )
  };

  /// Collapses the elements in `set` into a single value by starting with `base`
  /// and progessively combining elements into `base` with `combine`. Iteration runs
  /// right to left.
  ///
  /// Example:
  /// ```motoko
  /// import Set "mo:base/PersistentOrderedSet";
  /// import Nat "mo:base/Nat"
  /// import Iter "mo:base/Iter"
  /// import Debug "mo:base/Debug";
  ///
  /// let setOps = Set.SetOps<Nat>(Nat.compare);
  /// let set = setOps.fromIter(Iter.fromArray([0, 2, 1]));
  ///
  /// func folder(val : Nat, accum : Nat) : Nat = val + accum;
  ///
  /// Debug.print(debug_show(Set.foldRight(set, 0, folder)));
  ///
  /// // 3
  /// ```
  ///
  /// Cost of iteration over all elements:
  /// Runtime: `O(n)`.
  /// Space: depends on `combine` function plus garbage, see the note below.
  /// where `n` denotes the number of elements stored in the set.
  ///
  /// Note: Full set iteration creates `O(n)` temporary objects that will be collected as garbage.
  public func foldRight<T, Accum> (
    set : Set<T>,
    base : Accum,
    combine : (T, Accum) -> Accum
  ) : Accum
  {
    Map.foldRight(
      set,
      base,
      func (x : T , _ : (), acc : Accum) : Accum { combine(x, acc) }
    )
  };

  /// Test if the given set `s` is empty.
  ///
  /// Example:
  /// ```motoko
  /// import Set "mo:base/PersistentOrderedSet";
  /// import Debug "mo:base/Debug";
  ///
  /// let set = Set.empty<Nat>();
  ///
  /// Debug.print(debug_show(Set.isEmpty(set)));
  ///
  /// // true
  /// ```
  ///
  /// Runtime: `O(1)`.
  /// Space: `O(1)`
  public func isEmpty<T> (s : Set<T>) : Bool {
    switch s {
      case (#leaf) { true };
      case _ { false };
    };
  };
}
