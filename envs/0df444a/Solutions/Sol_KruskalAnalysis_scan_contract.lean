-- Prove2me | solution 1 for KruskalAnalysis.scan_contract
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:03:21.845958+00:00
-- url     : https://prove2.me/submissions/8f5f64a5-fa04-4423-858d-53136949e9c7

import Definitions.Def_Algo_kruskal_scan_Analysis
import Theorems.Thm_KruskalAnalysis_edge_contract


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
    | import_2 => cases location
    | fn_kruskal pc s =>
      have atLoop : pc = 4 := by
        unfold kruskal.At.scan at location
        split at location <;> simp_all
      subst pc
      change h = heap at heq
      subst h
      simp [kruskal.Local.chosen, kruskal.Local.index, kruskal.Local.count] at chosen idx cnt
      intro caller
      apply Reaches.prepend (Step.kruskal_pc4 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc3_false _ _ _ (by simp [idx, cnt]; omega))
      apply Reaches.prepend (Step.kruskal_pc2 _ _ _)
      simpa only [chosen] using Reaches.single (Step.kruskal_pc1 heap _ caller (by simpa [chosen]))



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
    | import_2 => cases location
    | fn_kruskal pc s =>
      have atLoop : pc = 4 := by
        unfold kruskal.At.scan at location
        split at location <;> simp_all
      subst pc
      change h = heap at heq
      subst h
      simp [kruskal.Local.sets, kruskal.Local.sources, kruskal.Local.targets,
        kruskal.Local.order, kruskal.Local.chosen, kruskal.Local.index, kruskal.Local.count]
        at sets src tgt ord chosen idx cnt
      intro caller
      apply Reaches.prepend (Step.kruskal_pc4 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc3_true _ _ _ (by simpa [idx, cnt]))
      apply Reaches.prepend (Step.kruskal_pc27 _ _ _ (by simpa [ord]))
      apply Reaches.prepend (Step.kruskal_pc26 _ _ _ (by simpa [src]))
      apply Reaches.prepend (Step.kruskal_pc25 _ _ _ (by simpa [tgt]))
      apply Reaches.prepend (Step.kruskal_pc24 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc23 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc22 _ _ _ (by simpa only [sets] using! findA.1))
      apply Reaches.prepend (Step.kruskal_pc21 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc20 _ _ _)
      simp only [sets, src, tgt, ord, chosen, idx] at *
      apply (ModuleCall.summary import_0_simulates _ caller findA.2).trans
      apply Reaches.prepend (Step.kruskal_pc19 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc18 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc17 _ _ _ (by exact findB.1))
      apply Reaches.prepend (Step.kruskal_pc16 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc15 _ _ _)
      apply (ModuleCall.summary import_0_simulates _ caller findB.2).trans
      apply Reaches.prepend (Step.kruskal_pc14 _ _ _)
      apply Reaches.prepend (Step.kruskal_pc13 _ _ _)
      by_cases distinct : left ≠ right
      · rw [if_pos distinct] at join
        obtain ⟨result, join⟩ := join
        apply Reaches.prepend (Step.kruskal_pc12_true _ _ _ (by simpa))
        apply Reaches.prepend (Step.kruskal_pc11 _ _ _ chosenAllocated)
        apply Reaches.prepend (Step.kruskal_pc10 _ _ _)
        apply Reaches.prepend (Step.kruskal_pc9 _ _ _ (by exact join.1))
        apply Reaches.prepend (Step.kruskal_pc8 _ _ _)
        apply Reaches.prepend (Step.kruskal_pc7 _ _ _)
        apply Reaches.prepend (Step.kruskal_pc6 _ _ _)
        apply (ModuleCall.summary import_0_simulates _ caller join.2).trans
        apply Reaches.prepend (Step.kruskal_pc5 _ _ _)
        refine rest (.active _ (.fn_kruskal 4 _) []) ?_ rfl caller
        exact ⟨True.intro, by simp [kruskal.Local.sets], by simp [kruskal.Local.sources],
          by simp [kruskal.Local.targets], by simp [kruskal.Local.order],
          by simp [kruskal.Local.chosen], by simp [kruskal.Local.index],
          by simp [kruskal.Local.count, cnt]⟩
      · rw [if_neg distinct] at join
        subst after
        apply Reaches.prepend (Step.kruskal_pc12_false _ _ _ (by simp [distinct]))
        apply Reaches.prepend (Step.kruskal_pc5 _ _ _)
        refine rest (.active _ (.fn_kruskal 4 _) []) ?_ rfl caller
        exact ⟨True.intro, by simp [kruskal.Local.sets], by simp [kruskal.Local.sources],
          by simp [kruskal.Local.targets], by simp [kruskal.Local.order],
          by simp [kruskal.Local.chosen], by simp [kruskal.Local.index],
          by simp [kruskal.Local.count, cnt]⟩





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






















end KruskalAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} (data : KruskalAnalysis.ScanLayout) (heap : Algo2LeanGenerated.Heap)
      (model : Algo2Lean.UnionFind.State n) (index count : Int)
      (pending selected : List.{0} Algo2Lean.Kruskal.Edge),
      KruskalAnalysis.ScanInvariant n data heap model index pending selected →
        Eq.{1} (HAdd.hAdd.{0, 0, 0} index (↑(List.length.{0} pending) : Int)) count →
          Exists.{1} fun final =>
            Exists.{1} fun nextModel =>
              Exists.{1} fun result =>
                KruskalAnalysis.ScanCall data heap index count final ∧
                  KruskalAnalysis.ScanInvariant n data final nextModel count List.nil.{0} result ∧
                    Algo2Lean.Kruskal.Scan pending selected result ∧
                      heap.Footprint final
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
                              Eq.{1} (final.clocks clock) (heap.clocks clock)) ∧
                          LE.le.{0} (KruskalAnalysis.work final.clocks)
                              (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work heap.clocks)
                                (HMul.hMul.{0, 0, 0} (List.length.{0} pending)
                                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (8 : Nat) n.log2)
                                    (6 : Nat)))) ∧
                            LE.le.{0}
                              (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work final.clocks)
                                (HMul.hMul.{0, 0, 0} (2 : Nat)
                                  (Algo2Lean.UnionFind.potential nextModel)))
                              (HAdd.hAdd.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.work heap.clocks)
                                  (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential model)))
                                (HMul.hMul.{0, 0, 0} (List.length.{0} pending)
                                  (HAdd.hAdd.{0, 0, 0}
                                    (HMul.hMul.{0, 0, 0} (10 : Nat) (Algo2Lean.Ackermann.alpha n))
                                    (14 : Nat)))) :=
  KruskalAnalysis.scan_contract
