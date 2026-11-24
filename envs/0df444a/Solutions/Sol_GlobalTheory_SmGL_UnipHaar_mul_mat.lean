-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.mul_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:10.57512+00:00
-- url     : https://prove2.me/submissions/1c1b8310-64e0-4680-90c0-e3479963031e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_ent_mul_mat

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
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution {A : Matrix n n R} (hA : A.BlockTriangular (blk e)) (x : Idx e → R) :
    A * mat e x = mat e ((lmat e A).mulVec x) := by
  rw [← ent_mul_mat]
  ext i j
  by_cases h : blk e i < blk e j
  · simp [mat, h, ent]
  · simp only [mat, of_apply, h, dif_neg, not_false_eq_true, mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h' : blk e l < blk e j
    · rw [hA (h'.trans_le (not_lt.1 h)), zero_mul]
    · simp [h']
end GlobalTheory.SmGL.UnipHaar
