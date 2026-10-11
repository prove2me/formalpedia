-- Prove2me | solution 1 for KruskalAnalysis.running_time
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:06:50.073143+00:00
-- url     : https://prove2.me/submissions/2ef13138-6fcf-4aaa-9767-c8e7744279ef

import Definitions.Def_Algo_kruskal_Analysis
import Theorems.Thm_KruskalAnalysis_call_complete


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

/-- An inserted forest edge cannot already occur in the remaining list. -/
theorem Forest.fresh {edge : Edge} {edges : List Edge} (forest : Forest (edge :: edges)) :
    edge ∉ edges := by
  intro member
  exact forest.2 (edge_connected member)

theorem Forest.nodup {edges : List Edge} (forest : Forest edges) : edges.Nodup := by
  induction edges with
  | nil => simp
  | cons edge rest ih => exact List.nodup_cons.mpr ⟨forest.fresh, ih forest.1⟩

/-- Joining different components cannot create an alternate route inside an
    existing component, even after some of that component's edges are removed. -/
theorem disconnected_extension {edge : Edge} {before after : List Edge} {u v : Int}
    (subset : ∀ candidate ∈ after, candidate ∈ before)
    (separate : ¬ Connected before edge.source edge.target)
    (old : Connected before u v) (path : Connected (edge :: after) u v) :
    Connected after u v := by
  rcases connected_cons.mp path with unchanged | forward | backward
  · exact unchanged
  · exact False.elim (separate ((forward.1.mono subset).symm.trans
      (old.trans (forward.2.mono subset).symm)))
  · exact False.elim (separate ((backward.2.mono subset).trans
      (old.symm.trans (backward.1.mono subset))))




/-- Every edge of a forest is a bridge. -/
theorem Forest.bridge {edges : List Edge} (forest : Forest edges)
    {edge : Edge} (member : edge ∈ edges) :
    ¬ Connected (edges.erase edge) edge.source edge.target := by
  induction edges with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simpa using forest.2
    · have different : first ≠ edge := by intro same; exact forest.fresh (same.symm ▸ member)
      simp only [List.erase_cons, beq_iff_eq, different, ↓reduceIte]
      intro path
      exact ih forest.1 member (disconnected_extension
        (fun _ included => List.mem_of_mem_erase included) forest.2
        (edge_connected member) path)













theorem weight_perm {one two : List Edge} (same : one.Perm two) : weight one = weight two := by
  induction same with
  | nil => rfl
  | cons edge same ih => simp [ih]
  | swap first second rest => simp [Int.add_left_comm]
  | trans first second ihOne ihTwo => exact ihOne.trans ihTwo












/-- The bridge characterization makes foresthood independent of list order. -/
theorem Forest.of_bridges {edges : List Edge}
    (bridges : ∀ edge ∈ edges, ¬ Connected (edges.erase edge) edge.source edge.target) :
    Forest edges := by
  induction edges with
  | nil => trivial
  | cons first rest ih =>
    have separate : ¬ Connected rest first.source first.target := by
      simpa using bridges first (by simp)
    refine ⟨ih ?_, separate⟩
    intro edge member path
    have different : first ≠ edge := by
      intro same
      exact separate (same.symm ▸ edge_connected member)
    apply bridges edge (by simp [member])
    simp only [List.erase_cons, beq_iff_eq, different, ↓reduceIte]
    exact path.mono (fun _ present => List.mem_cons_of_mem first present)

theorem Forest.perm {before after : List Edge} (forest : Forest before)
    (same : before.Perm after) : Forest after := by
  apply Forest.of_bridges
  intro edge member path
  apply forest.bridge (same.mem_iff.mpr member)
  exact path.mono (fun _ present => (same.erase edge).mem_iff.mpr present)







/-- A forest may be presented in output order rather than reverse insertion order. -/
theorem MinimumSpanningForest.perm_result {input before after : List Edge}
    (minimum : MinimumSpanningForest input before) (same : before.Perm after) :
    MinimumSpanningForest input after := by
  refine ⟨minimum.1.perm same, ⟨?_, ?_⟩, ?_⟩
  · exact fun edge member => minimum.2.1.subset edge (same.mem_iff.mpr member)
  · exact fun u v path => (minimum.2.1.connected u v path).mono
      (fun _ member => same.mem_iff.mp member)
  · intro other forest spanning
    rw [← weight_perm same]
    exact minimum.2.2 other forest spanning













end Algo2Lean.Kruskal

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












/-- An occurrence identifier uniquely determines an edge of the input graph. -/
theorem edge_eq_of_id {sources targets weights : Seq} {count : Int} {first second : Edge}
    (firstMember : first ∈ edges sources targets weights count)
    (secondMember : second ∈ edges sources targets weights count)
    (same : first.id = second.id) : first = second := by
  have firstValues := edge_contents firstMember
  have secondValues := edge_contents secondMember
  cases first
  cases second
  simp_all

/-- Reading the selected flags in input order gives the same minimum forest.
    This removes the proof's reverse insertion order from the public interface. -/
theorem minimum_from_flags {sources targets weights flags : Seq} {count : Int} {selected : List Edge}
    (minimum : MinimumSpanningForest (edges sources targets weights count) selected)
    (selection : ∀ id : Int,
      flags id = (if selected.any (fun edge => (edge.id : Int) == id) then 1 else 0)) :
    MinimumSpanningForest (edges sources targets weights count)
      ((edges sources targets weights count).filter (fun edge => flags edge.id == 1)) := by
  let input := edges sources targets weights count
  let result := input.filter (fun edge => flags edge.id == 1)
  have members (edge : Edge) : edge ∈ result ↔ edge ∈ selected := by
    constructor
    · intro member
      obtain ⟨inputMember, marked⟩ := List.mem_filter.mp member
      have present : selected.any (fun chosen => (chosen.id : Int) == (edge.id : Int)) = true := by
        have flag : flags edge.id = 1 := by simpa using marked
        rw [selection] at flag
        split at flag
        · assumption
        · contradiction
      obtain ⟨chosen, chosenMember, same⟩ := List.any_eq_true.mp present
      have ids : chosen.id = edge.id := by
        have castEqual : (chosen.id : Int) = (edge.id : Int) := by simpa using same
        omega
      have equal := edge_eq_of_id (minimum.2.1.subset chosen chosenMember) inputMember ids
      simpa [equal] using chosenMember
    · intro member
      apply List.mem_filter.mpr
      refine ⟨minimum.2.1.subset edge member, ?_⟩
      have present : selected.any (fun chosen => (chosen.id : Int) == (edge.id : Int)) = true :=
        List.any_eq_true.mpr ⟨edge, member, by simp⟩
      simp [selection, present]
  have inputUnique : input.Nodup :=
    List.Pairwise.of_map Edge.id (fun a b different same => different (congrArg Edge.id same))
      (edges_unique sources targets weights count)
  have resultUnique : result.Nodup := List.filter_sublist.nodup inputUnique
  have permutation : selected.Perm result := by
    apply List.perm_iff_count.mpr
    intro edge
    rw [minimum.1.nodup.count, resultUnique.count]
    simp only [members]
  exact minimum.perm_result permutation

end KruskalInput

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal's algorithm on finite undirected weighted graphs. The public interface
uses integer sequences for source vertices, target vertices, edge weights, and
returned selection flags. Correctness and running time reuse the independent
sorting, union-find, and graph analyses.
-/

namespace KruskalAnalysis

open Algo2LeanGenerated Algo.kruskal Algo2Lean.Kruskal
open KruskalInput





















/-- A compact value-and-work corollary of the full reusable call contract. -/
theorem call (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      runtime final.clocks ≤ runtime heap.clocks + runtimeBound size.toNat count.toNat := by
  obtain ⟨final, chosen, selected, execution, minimum, flags, bound, _⟩ :=
    call_complete heap size count sources targets weights allocated input
  exact ⟨final, chosen, selected, execution, minimum, flags, bound⟩









theorem load_valid (size count : Int) (sources targets weights : Seq) :
    kruskal.ValidInput (kruskal.load (size, sources, targets, weights, count)).1
      (size, 0, 1, 2, count) := by
  simp [kruskal.ValidInput, kruskal.load, Heap.allocate]



/-- Correctness and the complete operation bound share the same execution.
    All storage allocation and data-structure invariants are internal to the proof. -/
theorem verified {size count : Int} {sources targets weights chosen : Seq} {costs : Clocks}
    (input : WellFormed size count sources targets)
    (execution : kruskal.ReturnsWithCost (size, sources, targets, weights, count) chosen costs) :
    MinimumSpanningForest (edges sources targets weights count)
      (selectedEdges sources targets weights chosen count) ∧
      runtime costs ≤ runtimeBound size.toNat count.toNat := by
  obtain ⟨final, result, run, output, cost⟩ := execution
  let loaded := kruskal.load (size, sources, targets, weights, count)
  obtain ⟨expectedHeap, expectedResult, selected, summary, minimum, flags, bound⟩ :=
    call loaded.1 size count 0 1 2 (load_valid size count sources targets weights) input
  obtain ⟨rfl, rfl⟩ := run.eq_of_call summary
  have selection : Flags chosen selected := by
    rw [← output]
    exact flags
  refine ⟨minimum_from_flags minimum selection, ?_⟩
  have baseline : runtime loaded.1.clocks = 0 := by
    simp [loaded, runtime, SortIndicesAnalysis.runtime, Clocks.weighted, work, UnionFindAnalysis.work]
  have increments : Heap.cost loaded.1 final = final.clocks := by
    funext clock
    simp [Heap.cost, loaded]
  rw [← cost, increments]
  simpa only [baseline, Nat.zero_add] using bound

-- Main result: Correctness


-- Main result: Running time
/-- The total of all eight recorded operation clocks is bounded by
    2E(3 log2(E+1)+2) + V + 2 + E(10 alpha(V)+14). This is the source-level
    unit-cost model for integer arithmetic and sequence access. -/
theorem running_time {size count : Int} {sources targets weights chosen : Seq} {costs : Clocks}
    (input : WellFormed size count sources targets)
    (execution : kruskal.ReturnsWithCost (size, sources, targets, weights, count) chosen costs) :
    runtime costs ≤ runtimeBound size.toNat count.toNat :=
  (verified input execution).2



end KruskalAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {size count : Int} {sources targets weights chosen : Algo2LeanGenerated.Seq}
      {costs : Algo2LeanGenerated.Clocks},
      KruskalInput.WellFormed size count sources targets →
        Algo.kruskal.kruskal.ReturnsWithCost
            (Prod.mk.{0, 0} size
              (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
            chosen costs →
          LE.le.{0} (KruskalAnalysis.runtime costs)
            (KruskalAnalysis.runtimeBound size.toNat count.toNat) :=
  KruskalAnalysis.running_time
