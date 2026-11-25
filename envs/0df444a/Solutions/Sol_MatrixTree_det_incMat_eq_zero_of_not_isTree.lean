-- Prove2me | solution 1 for MatrixTree.det_incMat_eq_zero_of_not_isTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:31:09.076181+00:00
-- url     : https://prove2.me/submissions/a5e44bd0-3eb1-4f69-9e3f-b7d7b0627103

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_det_incMat_eq_zero_of_not_injective
public import Theorems.Thm_MatrixTree_det_incMat_eq_zero_of_not_reachable
public import Theorems.Thm_MatrixTree_card_ne_add_one

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace MatrixTree
theorem _root_.solution (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ∀ w, ¬ (g w).IsDiag) (hT : ¬ (fromEdgeSet (Set.range g)).IsTree) :
    (incMat v g).det = 0 := by
  by_cases hinj : Function.Injective g
  · obtain ⟨u, hu⟩ : ∃ u, ¬ (fromEdgeSet (Set.range g)).Reachable v u := by
      by_contra hc
      push Not at hc
      apply hT
      rw [isTree_iff_connected_and_card]
      refine ⟨(connected_iff _).mpr ⟨fun x y => (hc x).symm.trans (hc y), ⟨v⟩⟩, ?_⟩
      have hdisj : Set.range g \ Sym2.diagSet = Set.range g := by
        refine sdiff_eq_left.mpr (Set.disjoint_left.mpr ?_)
        rintro _ ⟨w, rfl⟩
        exact hg w
      rw [edgeSet_fromEdgeSet, hdisj, Nat.card_range_of_injective hinj]
      exact card_ne_add_one v
    exact det_incMat_eq_zero_of_not_reachable v g hg u hu
  · exact det_incMat_eq_zero_of_not_injective v g hinj
end MatrixTree
