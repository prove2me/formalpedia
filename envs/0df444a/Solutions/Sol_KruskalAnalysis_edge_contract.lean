-- Prove2me | solution 1 for KruskalAnalysis.edge_contract
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:02:06.890084+00:00
-- url     : https://prove2.me/submissions/51515077-7e4f-4091-a47e-9c979f46adf3

import Definitions.Def_Algo_kruskal_scan_Analysis
import Theorems.Thm_UnionFindAnalysis_find_contract
import Theorems.Thm_UnionFindAnalysis_union_summary_amortized
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





























































end Algo2Lean.Kruskal

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal initializes singleton components, sorts edge identifiers, and compares
representatives before selecting an edge and applying the verified union.
The graph argument is independent of the storage and transition machinery.
-/

namespace KruskalAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal Algo.kruskal.Algo2LeanGenerated
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























end KruskalAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} (data : KruskalAnalysis.ScanLayout) (heap : Algo2LeanGenerated.Heap)
      (model : Algo2Lean.UnionFind.State n) (index : Int) (edge : Algo2Lean.Kruskal.Edge)
      (pending selected : List.{0} Algo2Lean.Kruskal.Edge),
      KruskalAnalysis.ScanInvariant n data heap model index (List.cons.{0} edge pending) selected →
        Exists.{1} fun after =>
          Exists.{1} fun nextModel =>
            Exists.{1} fun accepted =>
              (Eq.{1} accepted Bool.true ↔
                  ¬Algo2Lean.Kruskal.Connected selected edge.source edge.target) ∧
                KruskalAnalysis.EdgeCalls data heap after (↑edge.id : Int) edge.source edge.target ∧
                  KruskalAnalysis.ScanInvariant n data after nextModel
                      (HAdd.hAdd.{0, 0, 0} index (1 : Int)) pending
                      (ite.{1} (Eq.{1} accepted Bool.true) (List.cons.{0} edge selected) selected) ∧
                    heap.Footprint after
                        (List.cons.{0} data.sets.parent
                          (List.cons.{0} data.sets.rank (List.cons.{0} data.chosen List.nil.{0})))
                        List.nil.{0} List.nil.{0} ∧
                      (∀ (clock : String),
                          ¬Membership.mem.{0, 0}
                                (List.cons.{0} "kruskal"
                                  (List.cons.{0} "uf_find"
                                    (List.cons.{0} "uf_compress"
                                      (List.cons.{0} "uf_union" List.nil.{0}))))
                                clock →
                            Eq.{1} (after.clocks clock) (heap.clocks clock)) ∧
                        LE.le.{0} (KruskalAnalysis.work after.clocks)
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work heap.clocks)
                                (HMul.hMul.{0, 0, 0} (8 : Nat) n.log2))
                              (6 : Nat)) ∧
                          LE.le.{0}
                            (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work after.clocks)
                              (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential nextModel)))
                            (HAdd.hAdd.{0, 0, 0}
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work heap.clocks)
                                  (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential model)))
                                (HMul.hMul.{0, 0, 0} (10 : Nat) (Algo2Lean.Ackermann.alpha n)))
                              (14 : Nat)) :=
  KruskalAnalysis.edge_contract
