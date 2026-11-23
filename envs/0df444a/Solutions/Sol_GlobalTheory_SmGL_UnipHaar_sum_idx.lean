-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.sum_idx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:53.05259+00:00
-- url     : https://prove2.me/submissions/694729a4-558c-44a3-be9a-7eeeb045bcde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable (e : (Σ a, m a) ≃ n)
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [DecidableEq n]
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution (f : n → n → R) (x : Idx e → R) :
    ∑ q : Idx e, f q.1.1 q.1.2 * x q = ∑ i, ∑ j, f i j * mat e x i j := by
  rw [← Fintype.sum_prod_type', ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : n × n => blk e p.1 < blk e p.2), Finset.sum_eq_zero (s := Finset.filter (fun p => ¬ _) _), add_zero,
    Finset.sum_subtype (p := fun p : n × n => blk e p.1 < blk e p.2) _ (by simp)]
  · exact Finset.sum_congr rfl fun q _ => by simp [mat, q.2]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [mat, hp]
end GlobalTheory.SmGL.UnipHaar
