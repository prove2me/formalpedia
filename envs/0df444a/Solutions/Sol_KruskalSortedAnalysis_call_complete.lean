-- Prove2me | solution 1 for KruskalSortedAnalysis.call_complete
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T01:54:02.13919+00:00
-- url     : https://prove2.me/submissions/2c10ff96-27e6-4f5e-a2c7-f1b736cd52ae

import Definitions.Def_Algo_kruskal_sorted_Analysis
import Theorems.Thm_UnionFindAnalysis_find_contract
import Theorems.Thm_UnionFindAnalysis_union_summary_amortized
import Theorems.Thm_UnionFindAnalysis_constructor_summary
import Theorems.Thm_UnionFindAnalysis_constructor_rep
import Theorems.Thm_Algo2Lean_Kruskal_Scan_minimum_spanning_forest
import Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Union-find mathematics for implementations using union by rank.

The parent and rank maps describe the stored data. Representatives and masses
are proof-only witnesses: a root owns the mass of its component, and linking
two roots transfers all losing mass to the winner. Starting from singleton
components gives a fixed mass budget of `n`. A root of rank `r` owns at least
`2 ^ r` mass, so every find follows at most `log₂ n` parent links.

Path compression preserves these bounds and the represented partition. The
module proves a logarithmic worst-case bound, not an inverse-Ackermann amortized
bound. It imports no generated algorithm or execution model.
-/

namespace Algo2Lean.UnionFind











theorem entry_le_total {n : Nat} (f : Fin n → Nat) (vertex : Fin n) :
    f vertex ≤ total f := by
  induction n with
  | zero => exact Fin.elim0 vertex
  | succ n ih =>
    refine Fin.cases ?_ (fun index => ?_) vertex
    · simp [total]
    · have bound := ih (fun index => f index.succ) index
      change f index.succ ≤ f 0 + total (fun index => f index.succ)
      omega

















theorem find_correct {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (run : Find state vertex root steps) :
    root = state.representative vertex ∧ state.parent root = root ∧
      state.rank vertex + steps ≤ state.rank root := by
  induction run with
  | root vertex fixed => exact ⟨(valid.root_representative vertex fixed).symm, fixed, by simp⟩
  | step vertex root steps moving _ ih =>
    obtain ⟨correct, fixed, bound⟩ := ih
    have rising := valid.parent_rank vertex moving
    exact ⟨correct.trans (valid.parent_representative vertex), fixed, by omega⟩

theorem root_rank_le_log {n : Nat} {state : State n} (valid : Valid state)
    (root : Fin n) (fixed : state.parent root = root) : state.rank root ≤ Nat.log2 n := by
  have massBound := Nat.le_trans (entry_le_total state.mass root) valid.mass_budget
  apply (Nat.le_log2 (by have := root.isLt; omega : n ≠ 0)).mpr
  exact Nat.le_trans (valid.root_mass root fixed) massBound

theorem find_cost {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (run : Find state vertex root steps) :
    steps ≤ Nat.log2 n := by
  obtain ⟨_, fixed, bounded⟩ := find_correct valid run
  have height := root_rank_le_log valid root fixed
  omega











































end Algo2Lean.UnionFind

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Inverse-Ackermann amortized analysis for union by rank and full path compression.

The Ackermann hierarchy and its least positive inverse are defined and proved
in `Algo2LeanLib.Ackermann`. This module uses the rank/level/iteration potential
argument of Cormen, Leiserson, Rivest, and Stein, Introduction to Algorithms,
second edition, §21.4. All definitions and proofs below are independent of
compiled programs and their heap representation.

A positive-rank nonroot records the largest Ackermann level below its parent's
rank and the number of iterations reached within that level. Its credit is
`alpha(n) * rank - (level * rank + iterations)`; a root has `alpha(n) * rank`
credit. A rank-zero node has zero credit. The global potential sums these
nonnegative credits over the fixed universe.

Path compression increases a node's hierarchy progress whenever its old level
occurs again later on the path. All but at most one rank-zero node and one node
per level therefore pay for their own traversed edge. A rank link can increase
credit only at the winning root, by at most `alpha(n)`. Scaling the potential
by two pays for both the find and compression events in the source cost model.

The reusable local results are `find_amortized` and `union_amortized`.
`Operations.from_initial` telescopes their bounds across arbitrary finite
operation sequences; `Operations.total_cost` includes initialization and gives
`n + 1 + 13 * (finds + unions) * alpha(n)`. The logarithmic worst-case bound
for an individual operation remains available from `Algo2LeanLib.UnionFind`.
-/

namespace Algo2Lean.UnionFind





























open Algo2Lean.Ackermann

noncomputable section











































































/-- Scaling credits by two pays one root test plus both events on every nonroot step. -/
theorem find_amortized {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps) :
    (2 * steps + 1) + 2 * potential (compressPath state vertex steps) ≤
      2 * potential state + 2 * alpha n + 3 := by
  have charged := compressPath_amortized valid path
  omega







-- Main result: Running time




end
end Algo2Lean.UnionFind

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Reusable contracts for the compiled union-find implementation.

`find_contract` and `union_contract` give the exact model, storage, and clock
effects of full path compression and union by rank. `find_amortized` and
`union_amortized` bound incremental work using a shared inverse-Ackermann
potential. The simpler `find_summary` and `union_summary` retain logarithmic
worst-case bounds, partition guarantees, and protection for caller storage.

The forest and rank invariants are independent of generated code and graphs.
Constructor correctness is in the companion `union_find_init` analysis. Costs
count the explicit source clocks and compose from arbitrary initial counters.
-/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated


















open Algo2Lean.UnionFind (State Find compress  find_correct find_cost )





/-- Charging a clock does not change the represented data structure. -/
theorem Rep.tick {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (clock : String) (amount : Nat := 1) :
    Rep (heap.tick clock amount) layout model :=
  ⟨representation.valid, representation.object, representation.readParent,
    representation.readRank, representation.readSize, representation.parentAllocated,
    representation.rankAllocated, representation.separate, representation.parents,
    representation.ranks⟩






































































/-- Exact increments add directly to total union-find work, even when the
    caller begins with nonzero counters. -/
theorem work_increments {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) :
    work after.clocks = work before.clocks + work costs := by
  simp only [work]
  rw [effect "uf_init", effect "uf_find", effect "uf_compress", effect "uf_union"]
  omega










-- Main result: Correctness and running time


end UnionFindAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Construction of the reusable rank-and-compression disjoint-set structure.
The constructor allocates one object and two arrays, initializes singleton
components, and charges exactly `n + 1` initialization ticks. -/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated







































/-- Initializing parents preserves every other sequence. -/
theorem initializeEntries_other (heap : Heap) (parent other : SeqRef)
    (first : Int) (count : Nat) (different : other ≠ parent) :
    (initializeEntries heap parent first count).read other = heap.read other := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeEntries, ih]
    funext index
    simp [Heap.read, Heap.write, different]





/-- Each initialized entry contributes one tick and changes no other clock. -/
theorem initializeEntries_clocks (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) (clock : String) :
    (initializeEntries heap parent first count).clocks clock =
      heap.clocks clock + if clock = "uf_init" then count else 0 := by
  induction count generalizing heap first with
  | zero => simp [initializeEntries]
  | succ count ih =>
    rw [initializeEntries, ih]
    by_cases same : clock = "uf_init" <;> simp [Heap.tick, same, Nat.add_assoc, Nat.add_comm]







/-- The constructor charges exactly one initial tick plus one per vertex. -/
theorem constructor_clocks (heap : Heap) (size : Nat) (clock : String) :
    (newHeap heap size).clocks clock = heap.clocks clock +
      if clock = "uf_init" then size + 1 else 0 := by
  simp only [newHeap, initializedHeap, initializeEntries_clocks]
  by_cases same : clock = "uf_init" <;>
    simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
      Heap.tick, same, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Constructor allocation adds exactly two integer sequences and one object,
    and leaves the collection allocation boundary unchanged. -/
theorem constructor_allocations (heap : Heap) (size : Nat) :
    (newHeap heap size).nextRef = heap.nextRef + 2 ∧
    (newHeap heap size).nextObject = heap.nextObject + 1 ∧
    (newHeap heap size).nextCollection = heap.nextCollection := by
  simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
    set_UnionFind_size, Nat.add_assoc]

/-- All old storage survives construction; the new arrays and object are fresh. -/
theorem constructor_frame (heap : Heap) (size : Nat) :
    (∀ ref, ref < heap.nextObject → (newHeap heap size).objects ref = heap.objects ref) ∧
    (∀ ref, ref < heap.nextRef → (newHeap heap size).read ref = heap.read ref) ∧
    (newHeap heap size).collections = heap.collections := by
  refine ⟨?_, ?_, ?_⟩
  · intro ref old
    simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
      set_UnionFind_size, Heap.writeField, Heap.allocateObject, Nat.ne_of_lt old]
  · intro ref old
    have different : ref ≠ heap.nextRef := Nat.ne_of_lt old
    simp only [newHeap, initializedHeap, Heap.allocateObject_nextRef,
      initializeEntries_other _ _ _ _ _ different]
    funext index
    simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
      Heap.read, Heap.allocate, different, show ref ≠ heap.nextRef + 1 by omega]
  · simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
      set_UnionFind_size]

-- Main result: Correctness and running time







/-- All existing storage is framed out of construction. Its object and arrays
    are fresh allocations, so its modification footprint is empty. -/
theorem constructor_footprint (heap : Heap) (size : Nat) :
    heap.Footprint (newHeap heap size) [] [] [] := by
  obtain ⟨objects, sequences, collections⟩ := constructor_frame heap size
  obtain ⟨nextRef, nextObject, nextCollection⟩ := constructor_allocations heap size
  refine ⟨by rw [nextRef]; omega, by rw [nextObject]; omega, by simp only [nextCollection, Nat.le_refl],
    ?_, ?_, ?_, ?_, ?_⟩
  · intro ref old
    simp only [Heap.objectClass, objects ref old]
  · intro ref old
    simp only [Heap.sequenceType, collections]
  · intro ref old _
    exact sequences ref old
  · intro ref old _
    exact objects ref old
  · intro ref old _
    rw [collections]





end UnionFindAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite undirected graph mathematics for Kruskal's algorithm. Edge identities
separate parallel input occurrences. Endpoints and weights are integers; weights
may be negative. This module does not depend on a union-find implementation or
on generated algorithm definitions.
-/

namespace Algo2Lean.Kruskal







theorem Adjacent.symm {edges : List Edge} {u v : Int} (edge : Adjacent edges u v) :
    Adjacent edges v u := by
  obtain ⟨e, member, forward | backward⟩ := edge
  · exact ⟨e, member, Or.inr forward⟩
  · exact ⟨e, member, Or.inl backward⟩

theorem Adjacent.connected {edges : List Edge} {u v : Int} (edge : Adjacent edges u v) :
    Connected edges u v := .step edge (.refl _)

theorem Connected.trans {edges : List Edge} {u v w : Int}
    (first : Connected edges u v) (second : Connected edges v w) : Connected edges u w := by
  induction first with
  | refl => exact second
  | step edge path ih => exact .step edge (ih second)

theorem Connected.symm {edges : List Edge} {u v : Int} (path : Connected edges u v) :
    Connected edges v u := by
  induction path with
  | refl => exact .refl _
  | step edge path ih => exact ih.trans edge.symm.connected

theorem Connected.mono {before after : List Edge} {u v : Int}
    (subset : ∀ edge ∈ before, edge ∈ after) (path : Connected before u v) :
    Connected after u v := by
  induction path with
  | refl => exact .refl _
  | step edge path ih =>
    obtain ⟨e, member, direction⟩ := edge
    exact .step ⟨e, subset e member, direction⟩ ih





theorem edge_connected {edges : List Edge} {edge : Edge} (member : edge ∈ edges) :
    Connected edges edge.source edge.target :=
  Adjacent.connected ⟨edge, member, Or.inl ⟨rfl, rfl⟩⟩
































theorem Joined.trans {edges : List Edge} {a b u v w : Int}
    (one : Joined edges a b u v) (two : Joined edges a b v w) :
    Joined edges a b u w := by
  rcases one with old | forward | backward
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inl (old.trans oldTwo)
    · exact Or.inr (Or.inl ⟨old.trans forwardTwo.1, forwardTwo.2⟩)
    · exact Or.inr (Or.inr ⟨old.trans backwardTwo.1, backwardTwo.2⟩)
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inr (Or.inl ⟨forward.1, forward.2.trans oldTwo⟩)
    · exact Or.inr (Or.inl ⟨forward.1, forwardTwo.2⟩)
    · exact Or.inl (forward.1.trans backwardTwo.2)
  · rcases two with oldTwo | forwardTwo | backwardTwo
    · exact Or.inr (Or.inr ⟨backward.1, backward.2.trans oldTwo⟩)
    · exact Or.inl (backward.1.trans forwardTwo.2)
    · exact Or.inr (Or.inr ⟨backward.1, backwardTwo.2⟩)

theorem connected_cons {edge : Edge} {edges : List Edge} {u v : Int} :
    Connected (edge :: edges) u v ↔ Joined edges edge.source edge.target u v := by
  constructor
  · intro path
    induction path with
    | refl => exact Or.inl (.refl _)
    | @step u next v adjacent rest ih =>
      apply Joined.trans (v := next) ?_ ih
      obtain ⟨candidate, member, direction⟩ := adjacent
      rcases List.mem_cons.mp member with rfl | member
      · rcases direction with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨.refl _, .refl _⟩)
        · exact Or.inr (Or.inr ⟨.refl _, .refl _⟩)
      · exact Or.inl (Adjacent.connected ⟨candidate, member, direction⟩)
  · intro joined
    have lift {x y} (path : Connected edges x y) : Connected (edge :: edges) x y :=
      path.mono (fun _ member => List.mem_cons_of_mem edge member)
    rcases joined with old | forward | backward
    · exact lift old
    · exact (lift forward.1).trans ((edge_connected (by simp)).trans (lift forward.2))
    · exact (lift backward.1).trans ((edge_connected (by simp)).symm.trans (lift backward.2))









































/-- Reordering input occurrences changes neither connectivity nor spanning. -/
theorem Spans.perm_input {before after selected : List Edge} (spanning : Spans before selected)
    (same : before.Perm after) : Spans after selected := by
  constructor
  · exact fun edge member => same.mem_iff.mp (spanning.subset edge member)
  · exact fun u v path => spanning.connected u v
      (path.mono (fun _ member => same.mem_iff.mpr member))

theorem MinimumSpanningForest.perm_input {before after selected : List Edge}
    (minimum : MinimumSpanningForest before selected) (same : before.Perm after) :
    MinimumSpanningForest after selected :=
  ⟨minimum.1, minimum.2.1.perm_input same,
    fun other forest spanning => minimum.2.2 other forest (spanning.perm_input same.symm)⟩

/-- Sorting may permute edge occurrences freely, including equal-weight edges.
    The result remains a minimum spanning forest of the original input. -/
theorem Scan.minimum_of_perm {input sorted result : List Edge}
    (permutation : input.Perm sorted) (ordered : Sorted sorted)
    (scan : Scan sorted [] result) : MinimumSpanningForest input result :=
  (scan.minimum_spanning_forest ordered).perm_input permutation.symm















end Algo2Lean.Kruskal

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The post-sorting Kruskal entry point initializes singleton components and
compares representatives before selecting an edge and applying the verified union.
The graph argument is independent of the storage and transition machinery.
-/

namespace KruskalAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal_sorted Algo.kruskal_sorted.Algo2LeanGenerated
open UnionFindAnalysis
open Algo2Lean.Kruskal














/-- Writing a client array leaves the union-find representation unchanged. -/
theorem Rep.write_client {n : Nat} {heap : Heap} {layout : Layout}
    {model : Algo2Lean.UnionFind.State n} (represented : Rep heap layout model)
    (ref : SeqRef) (index value : Int) (parent : ref ≠ layout.parent)
    (rank : ref ≠ layout.rank) : Rep (heap.write ref index value) layout model := by
  refine ⟨represented.valid, represented.object, represented.readParent,
    represented.readRank, represented.readSize, represented.parentAllocated,
    represented.rankAllocated, represented.separate, ?_, ?_⟩
  · intro vertex
    simpa [Heap.read, Heap.write, Ne.symm parent] using represented.parents vertex
  · intro vertex
    simpa [Heap.read, Heap.write, Ne.symm rank] using represented.ranks vertex

/-- Marking one identifier adds precisely that edge to the flag interpretation. -/
theorem Flags.select {heap : Heap} {chosen : SeqRef} {selected : List Edge}
    (flags : Flags (heap.read chosen) selected) (edge : Edge) (accepted : Bool) :
    Flags ((selectHeap heap chosen edge.id accepted).read chosen)
      (if accepted then edge :: selected else selected) := by
  cases accepted
  · exact flags
  · intro id
    by_cases same : id = (edge.id : Int)
    · subst id
      simp [selectHeap, Heap.read, Heap.write]
    · simp only [selectHeap, if_true]
      rw [Heap.read_write_other_index _ _ _ _ _ same, flags]
      simp [List.any_cons, show ¬ ((edge.id : Int) = id) from Ne.symm same]

/-- An unchanged order array represents the same pending edges. -/
theorem Order.congr {before after : Heap} {ref : SeqRef} {index : Int} {edges : List Edge}
    (ordered : Order before ref index edges) (same : after.read ref = before.read ref) :
    Order after ref index edges := by
  induction ordered with
  | nil index => exact .nil index
  | cons head tail ih => exact .cons (by simpa [same] using head) ih

/-- Adding an edge already inside a component does not alter connectivity. -/
theorem connected_redundant {selected : List Edge} {edge : Edge}
    (connected : Connected selected edge.source edge.target) (u v : Int) :
    Connected (edge :: selected) u v ↔ Connected selected u v := by
  constructor
  · intro path
    rcases connected_cons.mp path with old | forward | backward
    · exact old
    · exact forward.1.trans (connected.trans forward.2)
    · exact backward.1.trans (connected.symm.trans backward.2)
  · intro path
    exact connected_cons.mpr (Or.inl path)

/-- The union contract agrees with undirected graph connectivity, regardless
    of which root is chosen or which parent pointers are compressed. -/
theorem partition_join {n : Nat} {old next : Algo2Lean.UnionFind.State n}
    {selected : List Edge} {edge : Edge} (a b : Fin n)
    (source : (a.val : Int) = edge.source) (target : (b.val : Int) = edge.target)
    (partition : ∀ u v : Fin n, Algo2Lean.UnionFind.Connected old u v ↔
      Connected selected (u.val : Int) (v.val : Int))
    (joined : ∀ x y, Algo2Lean.UnionFind.Connected next x y ↔
      Algo2Lean.UnionFind.Connected old x y ∨
      (Algo2Lean.UnionFind.Connected old x a ∧ Algo2Lean.UnionFind.Connected old y b) ∨
      (Algo2Lean.UnionFind.Connected old x b ∧ Algo2Lean.UnionFind.Connected old y a)) :
    ∀ u v : Fin n, Algo2Lean.UnionFind.Connected next u v ↔
      Connected (edge :: selected) (u.val : Int) (v.val : Int) := by
  intro u v
  rw [joined, connected_cons]
  simp only [partition, source, target, Joined]
  constructor
  · rintro (old | ⟨first, second⟩ | ⟨first, second⟩)
    · exact Or.inl old
    · exact Or.inr (Or.inl ⟨first, second.symm⟩)
    · exact Or.inr (Or.inr ⟨first, second.symm⟩)
  · rintro (old | ⟨first, second⟩ | ⟨first, second⟩)
    · exact Or.inl old
    · exact Or.inr (Or.inl ⟨first, second.symm⟩)
    · exact Or.inr (Or.inr ⟨first, second.symm⟩)





/-- Completing an empty suffix returns the unchanged selection array. -/
theorem scan_done (data : ScanLayout) (heap : Heap) (index count : Int)
    (allocated : data.chosen < heap.nextRef) (finished : count ≤ index) :
    ScanCall data heap index count heap := by
  intro state reads heq
  rcases reads with ⟨location, sets, sources, targets, order, chosen, idx, cnt⟩
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | import_0 => cases location
    | fn_kruskal_sorted pc s =>
      have atLoop : pc = 4 := by
        unfold kruskal_sorted.At.scan at location
        split at location <;> simp_all
      subst pc
      change h = heap at heq
      subst h
      simp [kruskal_sorted.Local.chosen, kruskal_sorted.Local.index, kruskal_sorted.Local.count] at chosen idx cnt
      intro caller
      apply Reaches.prepend (Step.kruskal_sorted_pc4 _ _ _)
      apply Reaches.prepend (Step.kruskal_sorted_pc3_false _ _ _ (by simp [idx, cnt]; omega))
      apply Reaches.prepend (Step.kruskal_sorted_pc2 _ _ _)
      simpa only [chosen] using Reaches.single (Step.kruskal_sorted_pc1 heap _ caller (by simpa [chosen]))



/-- One source iteration reuses completed data-structure calls and the
    remaining loop, without exposing their internal transitions. -/
theorem scan_continue (data : ScanLayout) (heap after final : Heap) (index count : Int)
    (sources : data.sources < heap.nextRef) (targets : data.targets < heap.nextRef)
    (order : data.order < heap.nextRef) (running : index < count)
    (operations : EdgeCalls data heap after (heap.read data.order index)
      (heap.read data.sources (heap.read data.order index))
      (heap.read data.targets (heap.read data.order index)))
    (rest : ScanCall data after (index + 1) count final) :
    ScanCall data heap index count final := by
  obtain ⟨first, second, left, right, findA, findB, join, chosenAllocated⟩ := operations
  intro state reads heq
  rcases reads with ⟨location, sets, src, tgt, ord, chosen, idx, cnt⟩
  cases state with
  | done => cases location
  | active h frame originalStack =>
    cases frame with
    | invalid => cases location
    | import_0 => cases location
    | fn_kruskal_sorted pc s =>
      have atLoop : pc = 4 := by
        unfold kruskal_sorted.At.scan at location
        split at location <;> simp_all
      subst pc
      change h = heap at heq
      subst h
      simp [kruskal_sorted.Local.sets, kruskal_sorted.Local.sources, kruskal_sorted.Local.targets,
        kruskal_sorted.Local.order, kruskal_sorted.Local.chosen, kruskal_sorted.Local.index, kruskal_sorted.Local.count]
        at sets src tgt ord chosen idx cnt
      intro caller
      apply Reaches.prepend (Step.kruskal_sorted_pc4 _ _ _)
      apply Reaches.prepend (Step.kruskal_sorted_pc3_true _ _ _ (by simpa [idx, cnt]))
      apply Reaches.prepend (Step.kruskal_sorted_pc27 _ _ _ (by simpa [ord]))
      apply Reaches.prepend (Step.kruskal_sorted_pc26 _ _ _ (by simpa [src]))
      apply Reaches.prepend (Step.kruskal_sorted_pc25 _ _ _ (by simpa [tgt]))
      apply Reaches.prepend (Step.kruskal_sorted_pc24 _ _ _)
      apply Reaches.prepend (Step.kruskal_sorted_pc23 _ _ _)
      apply Reaches.prepend (Step.kruskal_sorted_pc22 _ _ _ (by simpa only [sets] using! findA.1))
      apply Reaches.prepend (Step.kruskal_sorted_pc21 _ _ _)
      apply Reaches.prepend (Step.kruskal_sorted_pc20 _ _ _)
      simp only [sets, src, tgt, ord, chosen, idx] at *
      apply (ModuleCall.summary import_0_simulates _ caller findA.2).trans
      apply Reaches.prepend (Step.kruskal_sorted_pc19 _ _ _)
      apply Reaches.prepend (Step.kruskal_sorted_pc18 _ _ _)
      apply Reaches.prepend (Step.kruskal_sorted_pc17 _ _ _ (by exact findB.1))
      apply Reaches.prepend (Step.kruskal_sorted_pc16 _ _ _)
      apply Reaches.prepend (Step.kruskal_sorted_pc15 _ _ _)
      apply (ModuleCall.summary import_0_simulates _ caller findB.2).trans
      apply Reaches.prepend (Step.kruskal_sorted_pc14 _ _ _)
      apply Reaches.prepend (Step.kruskal_sorted_pc13 _ _ _)
      by_cases distinct : left ≠ right
      · rw [if_pos distinct] at join
        obtain ⟨result, join⟩ := join
        apply Reaches.prepend (Step.kruskal_sorted_pc12_true _ _ _ (by simpa))
        apply Reaches.prepend (Step.kruskal_sorted_pc11 _ _ _ chosenAllocated)
        apply Reaches.prepend (Step.kruskal_sorted_pc10 _ _ _)
        apply Reaches.prepend (Step.kruskal_sorted_pc9 _ _ _ (by exact join.1))
        apply Reaches.prepend (Step.kruskal_sorted_pc8 _ _ _)
        apply Reaches.prepend (Step.kruskal_sorted_pc7 _ _ _)
        apply Reaches.prepend (Step.kruskal_sorted_pc6 _ _ _)
        apply (ModuleCall.summary import_0_simulates _ caller join.2).trans
        apply Reaches.prepend (Step.kruskal_sorted_pc5 _ _ _)
        refine rest (.active _ (.fn_kruskal_sorted 4 _) []) ?_ rfl caller
        exact ⟨True.intro, by simp [kruskal_sorted.Local.sets], by simp [kruskal_sorted.Local.sources],
          by simp [kruskal_sorted.Local.targets], by simp [kruskal_sorted.Local.order],
          by simp [kruskal_sorted.Local.chosen], by simp [kruskal_sorted.Local.index],
          by simp [kruskal_sorted.Local.count, cnt]⟩
      · rw [if_neg distinct] at join
        subst after
        apply Reaches.prepend (Step.kruskal_sorted_pc12_false _ _ _ (by simp [distinct]))
        apply Reaches.prepend (Step.kruskal_sorted_pc5 _ _ _)
        refine rest (.active _ (.fn_kruskal_sorted 4 _) []) ?_ rfl caller
        exact ⟨True.intro, by simp [kruskal_sorted.Local.sets], by simp [kruskal_sorted.Local.sources],
          by simp [kruskal_sorted.Local.targets], by simp [kruskal_sorted.Local.order],
          by simp [kruskal_sorted.Local.chosen], by simp [kruskal_sorted.Local.index],
          by simp [kruskal_sorted.Local.count, cnt]⟩
/-- One iteration preserves the graph representation and consumes the first
    pending edge. Only the two disjoint-set arrays and result flags may change. -/
theorem ScanInvariant.advance {n : Nat} {data : ScanLayout} {heap after : Heap}
    {model nextModel : Algo2Lean.UnionFind.State n} {index : Int}
    {edge : Edge} {pending selected : List Edge}
    (invariant : ScanInvariant n data heap model index (edge :: pending) selected)
    (represented : Rep after data.sets nextModel)
    (frame : heap.Footprint after [data.sets.parent, data.sets.rank, data.chosen] [] [])
    (partition : ∀ u v : Fin n, Algo2Lean.UnionFind.Connected nextModel u v ↔
      Connected (edge :: selected) (u.val : Int) (v.val : Int))
    (accepted : Bool)
    (decision : accepted = true ↔ ¬ Connected selected edge.source edge.target)
    (flags : Flags (after.read data.chosen) (if accepted then edge :: selected else selected)) :
    ScanInvariant n data after nextModel (index + 1) pending
      (if accepted then edge :: selected else selected) := by
  refine ⟨represented, ?_, ?_, ?_, ?_, ?_, flags,
    Nat.lt_of_lt_of_le invariant.sourceAllocated frame.nextRef,
    Nat.lt_of_lt_of_le invariant.targetAllocated frame.nextRef,
    Nat.lt_of_lt_of_le invariant.orderAllocated frame.nextRef,
    Nat.lt_of_lt_of_le invariant.chosenAllocated frame.nextRef,
    invariant.sourceProtected, invariant.targetProtected, invariant.orderProtected,
    invariant.chosenProtected⟩
  · intro u v
    cases accepted
    · have connected : Connected selected edge.source edge.target := by simpa using decision
      exact (partition u v).trans (connected_redundant connected _ _)
    · exact partition u v
  · intro next member
    exact invariant.bounded next (List.mem_cons_of_mem edge member)
  · intro next member
    rw [frame.read data.sources invariant.sourceAllocated invariant.sourceProtected]
    exact invariant.sources next (List.mem_cons_of_mem edge member)
  · intro next member
    rw [frame.read data.targets invariant.targetAllocated invariant.targetProtected]
    exact invariant.targets next (List.mem_cons_of_mem edge member)
  · cases invariant.ordered with
    | cons head tail => exact tail.congr (frame.read data.order invariant.orderAllocated invariant.orderProtected)

/-- Comparing two components performs two reusable full-compression finds.
    Connectivity and ranks are unchanged; costs telescope through the returned
    model instead of resetting the union-find potential between operations. -/
theorem compare_components {n : Nat} (heap : Heap) (layout : UnionFindAnalysis.Layout)
    (model : Algo2Lean.UnionFind.State n) (represented : Rep heap layout model) (a b : Fin n) :
    ∃ first second compressed,
      Algo.union_find.UnionFind.find.Call heap (layout.object, (a.val : Int)) first
        ((model.representative a).val : Int) ∧
      Algo.union_find.UnionFind.find.Call first (layout.object, (b.val : Int)) second
        ((model.representative b).val : Int) ∧
      Rep second layout compressed ∧ compressed.representative = model.representative ∧
      heap.Footprint second [layout.parent, layout.rank] [] [] ∧
      (∀ clock, clock ∉ ["uf_find", "uf_compress", "uf_union"] →
        second.clocks clock = heap.clocks clock) ∧
      UnionFindAnalysis.work second.clocks ≤ UnionFindAnalysis.work heap.clocks + 4 * n.log2 + 2 ∧
      UnionFindAnalysis.work second.clocks + 2 * Algo2Lean.UnionFind.potential compressed ≤
        UnionFindAnalysis.work heap.clocks + 2 * Algo2Lean.UnionFind.potential model +
          4 * Algo2Lean.Ackermann.alpha n + 6 := by
  obtain ⟨p, first, pathA, callA, repA, storageA, costsA⟩ := find_contract heap layout model represented a
  obtain ⟨q, second, pathB, callB, repB, storageB, costsB⟩ :=
    find_contract first layout (findResult model a p) repA b
  have sameA := findResult_representative model a p
  have sameB := findResult_representative (findResult model a p) b q
  have frame := storageA.footprint.trans storageB.footprint
  have firstWork := UnionFindAnalysis.work_increments costsA
  have secondWork := UnionFindAnalysis.work_increments costsB
  rw [work_findCosts] at firstWork secondWork
  have firstBound := Algo2Lean.UnionFind.find_cost represented.valid pathA
  have secondBound := Algo2Lean.UnionFind.find_cost repA.valid pathB
  have firstAmortized := Algo2Lean.UnionFind.find_amortized represented.valid pathA
  have secondAmortized := Algo2Lean.UnionFind.find_amortized repA.valid pathB
  refine ⟨first, second, _, callA, ?_, repB, sameB.trans sameA,
    frame.weaken (by simp) (by simp) (by simp), ?_, ?_, ?_⟩
  · simpa only [sameA] using callB
  · intro clock outside
    have different : clock ≠ "uf_find" ∧ clock ≠ "uf_compress" ∧ clock ≠ "uf_union" := by
      simpa using outside
    have ca := costsA clock
    have cb := costsB clock
    simp only [findCosts, different.1, different.2.1, if_false, Nat.add_zero] at ca cb
    omega
  · omega
  · change UnionFindAnalysis.work second.clocks +
      2 * Algo2Lean.UnionFind.potential (findResult (findResult model a p) b q) ≤ _
    simp only [findResult] at *
    omega

/-- The textbook edge test and conditional union reuse the independent find and
    union bounds. The rejected case performs no union and no selection write. -/
theorem edge_contract {n : Nat} (data : ScanLayout) (heap : Heap)
    (model : Algo2Lean.UnionFind.State n) (index : Int) (edge : Edge)
    (pending selected : List Edge)
    (invariant : ScanInvariant n data heap model index (edge :: pending) selected) :
    ∃ after nextModel, ∃ accepted : Bool,
      (accepted = true ↔ ¬ Connected selected edge.source edge.target) ∧
      EdgeCalls data heap after edge.id edge.source edge.target ∧
      ScanInvariant n data after nextModel (index + 1) pending
        (if accepted then edge :: selected else selected) ∧
      heap.Footprint after [data.sets.parent, data.sets.rank, data.chosen] [] [] ∧
      (∀ clock, clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"] →
        after.clocks clock = heap.clocks clock) ∧
      work after.clocks ≤ work heap.clocks + 8 * n.log2 + 6 ∧
      work after.clocks + 2 * Algo2Lean.UnionFind.potential nextModel ≤
        work heap.clocks + 2 * Algo2Lean.UnionFind.potential model +
          10 * Algo2Lean.Ackermann.alpha n + 14 := by
  classical
  obtain ⟨sourceBounds, targetBounds⟩ := invariant.bounded edge (by simp)
  let a : Fin n := ⟨edge.source.toNat, by omega⟩
  let b : Fin n := ⟨edge.target.toNat, by omega⟩
  have av : (a.val : Int) = edge.source := by simp [a]; omega
  have bv : (b.val : Int) = edge.target := by simp [b]; omega
  obtain ⟨first, second, compressed, findA, findB, rep, same, frame, clocks, cost, amortized⟩ :=
    compare_components (heap.tick "kruskal") data.sets model
      (invariant.representation.tick "kruskal") a b
  have samePartition (u v : Fin n) : Algo2Lean.UnionFind.Connected compressed u v ↔
      Algo2Lean.UnionFind.Connected model u v := by simp only [Algo2Lean.UnionFind.Connected, same]
  have separateChosen : data.chosen ≠ data.sets.parent ∧ data.chosen ≠ data.sets.rank := by
    simpa using invariant.chosenProtected
  have chosenAllocated : data.chosen < second.nextRef :=
    Nat.lt_of_lt_of_le invariant.chosenAllocated frame.nextRef
  have flags : Flags (second.read data.chosen) selected := by
    rw [frame.read data.chosen invariant.chosenAllocated invariant.chosenProtected]
    exact invariant.flags
  have beforeFrame := (Heap.Footprint.refl heap [data.sets.parent, data.sets.rank] [] []).tick "kruskal"
  have prefixFrame := beforeFrame.trans frame
  have ufTick : UnionFindAnalysis.work (heap.tick "kruskal").clocks =
      UnionFindAnalysis.work heap.clocks := by simp [UnionFindAnalysis.work, Heap.tick]
  rw [ufTick] at cost amortized
  have scanClock : second.clocks "kruskal" = heap.clocks "kruskal" + 1 := by
    simpa [Heap.tick] using clocks "kruskal" (by simp)
  by_cases distinct : model.representative a ≠ model.representative b
  · obtain ⟨after, nextModel, join, represented, joined, unionFrame, unionClocks, unionCost, unionAmortized⟩ :=
      union_summary_amortized (second.write data.chosen edge.id 1) data.sets compressed
        (Rep.write_client rep _ _ _ separateChosen.1 separateChosen.2) a b
    have writtenFrame := (prefixFrame.weaken
      (moreSequences := [data.sets.parent, data.sets.rank, data.chosen])
      (moreObjects := []) (moreCollections := [])
      (by simp) (by simp) (by simp)).write data.chosen edge.id 1 (Or.inl (by simp))
    have wholeFrame := writtenFrame.trans (unionFrame.weaken (by simp) (by simp) (by simp))
    have decision : decide (model.representative a ≠ model.representative b) = true ↔
        ¬ Connected selected edge.source edge.target := by
      simp only [decide_eq_true_eq]
      exact not_congr (by simpa only [Algo2Lean.UnionFind.Connected, av, bv] using invariant.partition a b)
    have partition := partition_join a b av bv
      (fun u v => (samePartition u v).trans (invariant.partition u v)) joined
    have finalFlags : Flags (after.read data.chosen) (edge :: selected) := by
      rw [unionFrame.read data.chosen chosenAllocated invariant.chosenProtected]
      simpa [selectHeap] using Flags.select (heap := second) (chosen := data.chosen) (edge := edge) flags true
    refine ⟨after, nextModel, true, ?_, ?_, ?_, wholeFrame, ?_, ?_, ?_⟩
    · simpa [distinct] using decision
    · refine ⟨first, second, ((model.representative a).val : Int), ((model.representative b).val : Int),
        ?_, ?_, ?_, chosenAllocated⟩
      · simpa only [av] using findA
      · simpa only [bv] using findB
      · have values : ((model.representative a).val : Int) ≠ ((model.representative b).val : Int) := by
          intro equal; apply distinct; apply Fin.ext; omega
        rw [if_pos values]
        exact ⟨_, by simpa only [av, bv] using join⟩
    · simpa only [dif_pos, if_pos, decide_eq_true distinct] using
        invariant.advance represented wholeFrame partition (decide (model.representative a ≠ model.representative b))
          decision (by simpa only [decide_eq_true distinct, if_true] using finalFlags)
    · intro clock outside
      have ns : clock ≠ "kruskal" := by simp_all
      have nu : clock ∉ ["uf_find", "uf_compress", "uf_union"] := by simp_all
      exact (unionClocks clock nu).trans (by simpa [Heap.tick, ns] using clocks clock nu)
    · have us := unionClocks "kruskal" (by simp)
      simp only [Heap.write_clocks] at unionCost us
      simp only [work]
      omega
    · have us := unionClocks "kruskal" (by simp)
      simp only [Heap.write_clocks] at unionAmortized us
      simp only [work]
      omega
  · have connected : Connected selected edge.source edge.target := by
      have eq : Algo2Lean.UnionFind.Connected model a b := by
        simpa [Algo2Lean.UnionFind.Connected] using distinct
      simpa only [av, bv] using (invariant.partition a b).mp eq
    have partition (u v : Fin n) : Algo2Lean.UnionFind.Connected compressed u v ↔
        Connected (edge :: selected) (u.val : Int) (v.val : Int) :=
      (samePartition u v).trans ((invariant.partition u v).trans (connected_redundant connected _ _).symm)
    have wholeFrame := prefixFrame.weaken
      (moreSequences := [data.sets.parent, data.sets.rank, data.chosen])
      (moreObjects := []) (moreCollections := []) (by simp) (by simp) (by simp)
    refine ⟨second, compressed, false, by simp [connected], ?_, ?_, wholeFrame, ?_, ?_, ?_⟩
    · refine ⟨first, second, ((model.representative a).val : Int), ((model.representative b).val : Int),
        ?_, ?_, ?_, chosenAllocated⟩
      · simpa only [av] using findA
      · simpa only [bv] using findB
      · have values : ((model.representative a).val : Int) = ((model.representative b).val : Int) := by
          simp_all
        simp [values]
    · simpa only [decide_eq_false distinct, Bool.false_eq_true, if_false] using
        invariant.advance rep wholeFrame partition false (by simp [connected]) flags
    · intro clock outside
      have ns : clock ≠ "kruskal" := by simp_all
      have nu : clock ∉ ["uf_find", "uf_compress", "uf_union"] := by simp_all
      simpa [Heap.tick, ns] using clocks clock nu
    · simp only [work]; omega
    · simp only [work]; omega
/-- The edge loop terminates and follows the abstract Kruskal scan. Each edge
    costs two finds and, only when accepted, a union; potentials telescope
    across every call on the same mutable disjoint-set object. -/
theorem scan_contract {n : Nat} (data : ScanLayout) (heap : Heap)
    (model : Algo2Lean.UnionFind.State n) (index count : Int) (pending selected : List Edge)
    (invariant : ScanInvariant n data heap model index pending selected)
    (length : index + (pending.length : Int) = count) :
    ∃ final nextModel result,
      ScanCall data heap index count final ∧
      ScanInvariant n data final nextModel count [] result ∧
      Scan pending selected result ∧
      heap.Footprint final [data.sets.parent, data.sets.rank, data.chosen] [] [] ∧
      (∀ clock, clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"] →
        final.clocks clock = heap.clocks clock) ∧
      work final.clocks ≤ work heap.clocks + pending.length * (8 * n.log2 + 6) ∧
      work final.clocks + 2 * Algo2Lean.UnionFind.potential nextModel ≤
        work heap.clocks + 2 * Algo2Lean.UnionFind.potential model +
          pending.length * (10 * Algo2Lean.Ackermann.alpha n + 14) := by
  classical
  induction pending generalizing heap model index selected with
  | nil =>
    have finish : index = count := by simpa using length
    subst index
    exact ⟨heap, model, selected, scan_done data heap count count invariant.chosenAllocated (by omega),
      invariant, .done selected, Heap.Footprint.refl _ _ _ _, by intros; rfl, by simp, by simp⟩
  | cons edge pending ih =>
    obtain ⟨after, nextModel, accepted, decision, operations, nextInvariant, frame, clocks, cost, amortized⟩ :=
      edge_contract data heap model index edge pending selected invariant
    have shorter : index + 1 + (pending.length : Int) = count := by
      simp only [List.length_cons] at length
      omega
    obtain ⟨final, finalModel, result, rest, finalInvariant, scan, suffixFrame, suffixClocks, suffixCost, suffixAmortized⟩ :=
      ih after nextModel (index + 1) (if accepted then edge :: selected else selected) nextInvariant shorter
    have edgeId : heap.read data.order index = (edge.id : Int) := by
      cases invariant.ordered with
      | cons head _ => exact head
    have sourceRead : heap.read data.sources (heap.read data.order index) = edge.source := by
      rw [edgeId]
      exact invariant.sources edge (by simp)
    have targetRead : heap.read data.targets (heap.read data.order index) = edge.target := by
      rw [edgeId]
      exact invariant.targets edge (by simp)
    refine ⟨final, finalModel, result, ?_, finalInvariant, ?_, frame.trans suffixFrame, ?_, ?_, ?_⟩
    · apply scan_continue data heap after final index count invariant.sourceAllocated
        invariant.targetAllocated invariant.orderAllocated (by simp only [List.length_cons] at length; omega)
      · rw [sourceRead, targetRead, edgeId]
        exact operations
      · exact rest
    · cases hacc : accepted with
      | false =>
        have connected : Connected selected edge.source edge.target := by simpa [hacc] using decision
        exact Scan.reject connected (by simpa [hacc] using scan)
      | true =>
        exact Scan.accept (decision.mp hacc) (by simpa [hacc] using scan)
    · intro clock outside
      exact (suffixClocks clock outside).trans (clocks clock outside)
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega



/-- A finite array prefix determines the inductive order view. -/
theorem Order.of_indexed (heap : Heap) (ref : SeqRef) (index : Int) (pending : List Edge)
    (agreement : ∀ (i : Nat) (within : i < pending.length),
      heap.read ref (index + i) = (pending[i].id : Int)) : Order heap ref index pending := by
  induction pending generalizing index with
  | nil => exact .nil index
  | cons edge pending ih =>
    apply Order.cons
    · simpa using agreement 0 (by simp)
    · apply ih (index + 1)
      intro i within
      have shifted := agreement (i + 1) (by simpa using within)
      have indexEq : index + (↑(i + 1) : Int) = index + 1 + i := by omega
      rw [indexEq] at shifted
      simpa only [List.getElem_cons_succ] using shifted

/-- A disjoint-set representation survives a call that preserves existing
    storage. This is the only fact about sorting needed by the union-find model. -/
theorem Rep.preserve {n : Nat} {before after : Heap} {layout : UnionFindAnalysis.Layout}
    {model : Algo2Lean.UnionFind.State n} (rep : Rep before layout model)
    (frame : before.Footprint after [] [] []) : Rep after layout model := by
  open Algo.union_find.Algo2LeanGenerated in
    have object : is_UnionFind after layout.object :=
      ⟨Nat.lt_of_lt_of_le rep.object.1 frame.nextObject,
        (frame.classes layout.object rep.object.1).trans rep.object.2⟩
    refine ⟨rep.valid, object, ?_, ?_, ?_,
      Nat.lt_of_lt_of_le rep.parentAllocated frame.nextRef,
      Nat.lt_of_lt_of_le rep.rankAllocated frame.nextRef, rep.separate, ?_, ?_⟩
    · simpa only [field_UnionFind_parent, if_pos object,
        frame.readField layout.object rep.object.1 (by simp), if_pos rep.object] using rep.readParent
    · simpa only [field_UnionFind_rank, if_pos object,
        frame.readField layout.object rep.object.1 (by simp), if_pos rep.object] using rep.readRank
    · simpa only [field_UnionFind_size, if_pos object,
        frame.readField layout.object rep.object.1 (by simp), if_pos rep.object] using rep.readSize
    · intro vertex
      rw [frame.read layout.parent rep.parentAllocated (by simp)]
      exact rep.parents vertex
    · intro vertex
      rw [frame.read layout.rank rep.rankAllocated (by simp)]
      exact rep.ranks vertex





/-- Initialization preserves every caller location while creating private data. -/
theorem initial_footprint (heap : Heap) (size : Nat) :
    heap.Footprint (initialHeap heap size) [] [] [] :=
  ((Heap.Footprint.refl heap [] [] []).allocate (fun _ => 0)).trans
    (constructor_footprint (heap.allocate (fun _ => 0)) size)

/-- Initialization preserves all previously allocated sequence values. -/
theorem initial_read_old (heap : Heap) (size : Nat) (ref : SeqRef) (old : ref < heap.nextRef) :
    (initialHeap heap size).read ref = heap.read ref :=
  (initial_footprint heap size).read ref old (by simp)

/-- A preserved initialized heap and a protected edge order establish the scan invariant. -/
theorem initial_invariant (heap sorted : Heap) (size : Nat) (sources targets order : SeqRef)
    (pending : List Edge)
    (sourceAllocated : sources < heap.nextRef) (targetAllocated : targets < heap.nextRef)
    (frame : (initialHeap heap size).Footprint sorted [] [] [])
    (orderProtected : order ∉ [(initialLayout heap size sources targets order).sets.parent,
      (initialLayout heap size sources targets order).sets.rank, heap.nextRef])
    (orderAllocated : order < sorted.nextRef)
    (bounds : ValidInput size pending)
    (sourceValues : ∀ edge ∈ pending, heap.read sources edge.id = edge.source)
    (targetValues : ∀ edge ∈ pending, heap.read targets edge.id = edge.target)
    (ordering : ∀ (i : Nat) (within : i < pending.length), sorted.read order i = (pending[i].id : Int)) :
    ScanInvariant size (initialLayout heap size sources targets order) (sorted.tick "kruskal")
      (Algo2Lean.UnionFind.initial size) 0 pending [] := by
  have refs : (initialHeap heap size).nextRef = heap.nextRef + 3 := by
    simpa [initialHeap, Heap.allocate] using (constructor_allocations (heap.allocate (fun _ => 0)) size).1
  have initFrame := initial_footprint heap size
  have whole := initFrame.trans frame
  have chosenInit : heap.nextRef < (initialHeap heap size).nextRef := by rw [refs]; omega
  have chosenValues : (initialHeap heap size).read heap.nextRef = (fun _ => 0) := by
    have preserve := (constructor_frame (heap.allocate (fun _ => 0)) size).2.1 heap.nextRef (by simp [Heap.allocate])
    change (newHeap (heap.allocate (fun _ => 0)) size).read heap.nextRef = _
    rw [preserve]
    funext index
    exact Heap.read_allocate_new heap (fun _ => 0) index
  have represented := Rep.preserve (constructor_rep (heap.allocate (fun _ => 0)) size) frame
  refine ⟨represented.tick "kruskal", ?_,
    (fun edge member => ⟨bounds.source edge member, bounds.target edge member⟩), ?_, ?_, ?_, ?_,
    Nat.lt_of_lt_of_le sourceAllocated whole.nextRef,
    Nat.lt_of_lt_of_le targetAllocated whole.nextRef, orderAllocated,
    Nat.lt_of_lt_of_le chosenInit frame.nextRef, ?_, ?_, ?_, ?_⟩
  · intro u v
    rw [Algo2Lean.UnionFind.initial_connected, connected_nil]
    constructor
    · intro same; subst v; rfl
    · intro same; apply Fin.ext; omega
  · intro edge member
    change sorted.read sources edge.id = edge.source
    rw [whole.read sources sourceAllocated (by simp)]
    exact sourceValues edge member
  · intro edge member
    change sorted.read targets edge.id = edge.target
    rw [whole.read targets targetAllocated (by simp)]
    exact targetValues edge member
  · apply Order.of_indexed
    intro i within
    change sorted.read order (0 + i) = _
    simpa only [Int.zero_add] using ordering i within
  · intro id
    change sorted.read heap.nextRef id = _
    rw [frame.read heap.nextRef chosenInit (by simp), chosenValues]
    simp
  · simp only [initialLayout, newLayout, Heap.allocate_nextRef, List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [SeqRef] at *
    omega
  · simp only [initialLayout, newLayout, Heap.allocate_nextRef, List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [SeqRef] at *
    omega
  · exact orderProtected
  · simp only [initialLayout, newLayout, Heap.allocate_nextRef, List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [SeqRef] at *
    omega

/-- Constructing all singleton components costs V+1 initialization ticks. -/
theorem initial_work (heap : Heap) (size : Nat) :
    work (initialHeap heap size).clocks = work heap.clocks + size + 1 := by
  simp [work, UnionFindAnalysis.work, initialHeap, constructor_clocks]
  omega

/-- Initialization changes only the union-find initialization clock. -/
theorem initial_clocks (heap : Heap) (size : Nat) (clock : String)
    (notInit : clock ≠ "uf_init") :
    (initialHeap heap size).clocks clock = heap.clocks clock := by
  simp [initialHeap, constructor_clocks, notInit]

end KruskalAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The graph supplied to the source program consists of three integer sequences
and a finite edge count. This module translates that representation into the
finite graph model and connects the reusable sorting theorem to Kruskal's scan.
-/

open Algo2LeanGenerated Algo2Lean.Kruskal

namespace KruskalInput











/-- Distinct positions give distinct edge identities, including parallel edges. -/
theorem edges_unique (sources targets weights : Seq) (count : Int) :
    ((edges sources targets weights count).map Edge.id).Nodup := by
  rw [edges_ids]
  exact List.nodup_range

/-- Membership connects the graph model back to the original endpoint arrays. -/
theorem edge_contents {sources targets weights : Seq} {count : Int} {edge : Edge}
    (member : edge ∈ edges sources targets weights count) :
    (edge.id : Int) < count ∧ sources edge.id = edge.source ∧
      targets edge.id = edge.target ∧ weights edge.id = edge.weight := by
  obtain ⟨identifier, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨nonnegative, within⟩ := (Algo2Lean.FiniteIndex.range_member count identifier).mp present
  simpa only [edgeAt, Int.toNat_of_nonneg nonnegative] using
    (show identifier < count ∧ sources identifier = sources identifier ∧
      targets identifier = targets identifier ∧ weights identifier = weights identifier from
      ⟨within, rfl, rfl, rfl⟩)

theorem WellFormed.valid {size count : Int} {sources targets : Seq}
    (input : WellFormed size count sources targets) (weights : Seq) :
    ValidInput size.toNat (edges sources targets weights count) := by
  refine ⟨edges_unique _ _ _ _, ?_, ?_⟩
  · intro edge member
    obtain ⟨within, source, target, weight⟩ := edge_contents member
    have bound := input.source_bounds edge.id (by omega) within
    rw [source] at bound
    exact ⟨bound.1, by omega⟩
  · intro edge member
    obtain ⟨within, source, target, weight⟩ := edge_contents member
    have bound := input.target_bounds edge.id (by omega) within
    rw [target] at bound
    exact ⟨bound.1, by omega⟩



/-- Sort the identifiers once, then obtain the sorted graph view without
    unfolding the sorting algorithm or repeating a heap proof. -/
theorem sorted_edges (sources targets weights order : Seq) (count : Int)
    (sorting : SortIndicesAnalysis.SortedPermutation weights count order) :
    ∃ pending, SortedEdges sources targets weights order count pending := by
  obtain ⟨identifiers, permutation, sorted, agreement⟩ := sorting
  let pending := identifiers.map (edgeAt sources targets weights)
  have mapped : (edges sources targets weights count).Perm pending := permutation.symm.map _
  have memberContents (edge : Edge) (member : edge ∈ pending) :=
    edge_contents (mapped.mem_iff.mpr member)
  refine ⟨pending, mapped, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sorted.map (edgeAt sources targets weights) (by intros; assumption)
  · exact mapped.length_eq.symm.trans (edges_length _ _ _ _)
  · intro index within
    have bound : index < identifiers.length := by simpa [pending] using within
    have original : identifiers[index] ∈ Algo2Lean.FiniteIndex.range count :=
      permutation.mem_iff.mp (List.getElem_mem bound)
    have nonnegative := ((Algo2Lean.FiniteIndex.range_member _ _).mp original).1
    have agrees := agreement index bound
    simpa [pending, edgeAt, getElem!_pos, bound, Int.toNat_of_nonneg nonnegative] using agrees
  · exact fun edge member => (memberContents edge member).2.1
  · exact fun edge member => (memberContents edge member).2.2.1
  · exact fun edge member => (memberContents edge member).2.2.2
  · exact fun edge member => (memberContents edge member).1

theorem SortedEdges.valid {size count : Int} {sources targets weights order : Seq} {pending : List Edge}
    (sorting : SortedEdges sources targets weights order count pending)
    (input : WellFormed size count sources targets) : ValidInput size.toNat pending := by
  constructor
  · exact (input.valid weights).identities.perm (sorting.permutation.map Edge.id)
  · intro edge member
    exact (input.valid weights).source edge (sorting.permutation.mem_iff.mpr member)
  · intro edge member
    exact (input.valid weights).target edge (sorting.permutation.mem_iff.mpr member)

/-- The scan's graph theorem applies directly to the original array input. -/
theorem SortedEdges.minimum {sources targets weights order : Seq} {count : Int}
    {pending selected : List Edge}
    (sorting : SortedEdges sources targets weights order count pending)
    (scan : Scan pending [] selected) : MinimumSpanningForest (edges sources targets weights count) selected :=
  scan.minimum_of_perm sorting.permutation sorting.sorted






end KruskalInput

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal after sorting: a caller supplies a permutation of the original edge
identifiers in nondecreasing weight order. The source allocates singleton
components and scans that order; it performs no sorting. The reusable Call
contract combines the graph exchange argument with the independently proved
inverse-Ackermann contracts for union by rank and full path compression.
-/

namespace KruskalSortedAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal_sorted Algo.kruskal_sorted.Algo2LeanGenerated
open Algo2Lean.Kruskal KruskalInput KruskalAnalysis











/-- The source constructs singleton components and enters its edge scan directly. -/
theorem sorted_calls (heap initialized final : Heap)
    (size count : Int) (sources targets weights order : SeqRef) (sets : UnionFindAnalysis.Layout)
    (valid : kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order))
    (construction : Algo.union_find.UnionFind.Call (heap.allocate (fun _ => 0)) size initialized sets.object)
    (scan : ScanCall ⟨sets, sources, targets, order, heap.nextRef⟩
      (initialized.tick "kruskal") 0 count final) :
    kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final heap.nextRef := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.kruskal_sorted_pc35 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc34 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc33 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc32 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc31 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller construction.2).trans
  apply Reaches.prepend (Step.kruskal_sorted_pc30 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc29 _ _ _)
  apply Reaches.prepend (Step.kruskal_sorted_pc28 _ _ _)
  refine scan (.active _ (.fn_kruskal_sorted 4 _) []) ?_ rfl caller
  exact ⟨True.intro, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- On a supplied sorted order, initialization and the verified edge scan
    terminate with a fresh minimum spanning forest. Old caller storage remains
    unchanged, including all input arrays and their possible aliases. -/
theorem call_complete (heap : Heap) (size count : Int) (sources targets weights order : SeqRef)
    (allocated : kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order))
    (input : WellFormed size count (heap.read sources) (heap.read targets))
    (ordered : SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order)) :
    ∃ final chosen selected,
      kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      runtime final.clocks ≤ runtime heap.clocks + runtimeBound size.toNat count.toNat ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
      (∀ clock, clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
        final.clocks clock = heap.clocks clock) := by
  let initialized := initialHeap heap size.toNat
  have initFrame := initial_footprint heap size.toNat
  obtain ⟨pending, sorting⟩ := sorted_edges (heap.read sources) (heap.read targets)
    (heap.read weights) (heap.read order) count ordered
  have orderPrivate : order ∉ [(initialLayout heap size.toNat sources targets order).sets.parent,
      (initialLayout heap size.toNat sources targets order).sets.rank, heap.nextRef] := by
    simp only [initialLayout, UnionFindAnalysis.newLayout, Heap.allocate_nextRef,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    have old := allocated.2.2.2
    simp only [SeqRef] at *
    omega
  have initial := initial_invariant heap initialized size.toNat sources targets order pending
    allocated.1 allocated.2.1 (Heap.Footprint.refl _ [] [] []) orderPrivate
    (Nat.lt_of_lt_of_le allocated.2.2.2 initFrame.nextRef) (sorting.valid input)
    sorting.source sorting.target (by
      intro i within
      rw [initial_read_old heap size.toNat order allocated.2.2.2]
      exact sorting.order i within)
  obtain ⟨final, model, selected, scanCall, finalInvariant, scan, frame, clocks, worstCase, bound⟩ :=
    scan_contract (initialLayout heap size.toNat sources targets order)
      (initialized.tick "kruskal") (Algo2Lean.UnionFind.initial size.toNat) 0 count pending []
      initial (by rw [sorting.length]; have nonnegative := input.count_nonnegative; omega)
  have composed := sorted_calls heap initialized final size count sources targets weights order
    (UnionFindAnalysis.newLayout (heap.allocate (fun _ => 0))) allocated
    (by simpa only [initialized, initialHeap, UnionFindAnalysis.newLayout,
      Int.toNat_of_nonneg input.size_nonnegative] using!
      UnionFindAnalysis.constructor_summary (heap.allocate (fun _ => 0)) size.toNat)
    scanCall
  have wholeFrame := ((initFrame.tick "kruskal").weaken
    (moreSequences := [(initialLayout heap size.toNat sources targets order).sets.parent,
      (initialLayout heap size.toNat sources targets order).sets.rank,
      (initialLayout heap size.toNat sources targets order).chosen])
    (moreObjects := []) (moreCollections := []) (by simp) (by simp) (by simp)).trans frame
  have preservedClocks : ∀ clock,
      clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
      final.clocks clock = heap.clocks clock := by
    intro clock outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    rw [clocks clock (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨outside.2.2.2.2, outside.2.1, outside.2.2.1, outside.2.2.2.1⟩)]
    simp only [Heap.tick, if_neg outside.2.2.2.2]
    exact initial_clocks heap size.toNat clock outside.1
  refine ⟨final, heap.nextRef, selected, composed, sorting.minimum scan, finalInvariant.flags,
    ?_, ?_, Nat.le_refl _, finalInvariant.chosenAllocated, preservedClocks⟩
  · have initialWork := initial_work heap size.toNat
    have tickWork : work (initialized.tick "kruskal").clocks = work initialized.clocks + 1 := by
      simp [work, UnionFindAnalysis.work, Heap.tick]; omega
    rw [tickWork, initialWork, sorting.length, Algo2Lean.UnionFind.initial_potential] at bound
    have sortUnchanged : SortIndicesAnalysis.runtime final.clocks = SortIndicesAnalysis.runtime heap.clocks := by
      simp only [SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      rw [preservedClocks "sort_steps" (by decide), preservedClocks "heap_comparisons" (by decide),
        preservedClocks "heap_swaps" (by decide)]
    simp only [runtime, runtimeBound]
    rw [sortUnchanged]
    omega
  · refine ⟨wholeFrame.nextRef, wholeFrame.nextObject, wholeFrame.nextCollection,
      wholeFrame.classes, wholeFrame.types, ?_, wholeFrame.otherObjects, wholeFrame.otherCollections⟩
    intro ref old _
    apply wholeFrame.otherSequences ref old
    simp only [initialLayout, UnionFindAnalysis.newLayout, Heap.allocate_nextRef,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [SeqRef] at *
    omega




-- Main result: Correctness and running time
























end KruskalSortedAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (size count : Int)
      (sources targets weights order : Algo2LeanGenerated.SeqRef),
      Algo.kruskal_sorted.kruskal_sorted.ValidInput heap
          (Prod.mk.{0, 0} size
            (Prod.mk.{0, 0} sources
              (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights (Prod.mk.{0, 0} count order))))) →
        KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
          SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order) →
            Exists.{1} fun final =>
              Exists.{1} fun chosen =>
                Exists.{1} fun selected =>
                  Algo.kruskal_sorted.kruskal_sorted.Call heap
                      (Prod.mk.{0, 0} size
                        (Prod.mk.{0, 0} sources
                          (Prod.mk.{0, 0} targets
                            (Prod.mk.{0, 0} weights (Prod.mk.{0, 0} count order)))))
                      final chosen ∧
                    Algo2Lean.Kruskal.MinimumSpanningForest
                        (KruskalInput.edges (heap.read sources) (heap.read targets) (heap.read weights)
                          count)
                        selected ∧
                      KruskalAnalysis.Flags (final.read chosen) selected ∧
                        LE.le.{0} (KruskalSortedAnalysis.runtime final.clocks)
                            (HAdd.hAdd.{0, 0, 0} (KruskalSortedAnalysis.runtime heap.clocks)
                              (KruskalSortedAnalysis.runtimeBound size.toNat count.toNat)) ∧
                          heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                            LE.le.{0} heap.nextRef chosen ∧
                              LT.lt.{0} chosen final.nextRef ∧
                                ∀ (clock : String),
                                  ¬Membership.mem.{0, 0}
                                        (List.cons.{0} "uf_init"
                                          (List.cons.{0} "uf_find"
                                            (List.cons.{0} "uf_compress"
                                              (List.cons.{0} "uf_union"
                                                (List.cons.{0} "kruskal" List.nil.{0})))))
                                        clock →
                                    Eq.{1} (final.clocks clock) (heap.clocks clock) :=
  KruskalSortedAnalysis.call_complete
