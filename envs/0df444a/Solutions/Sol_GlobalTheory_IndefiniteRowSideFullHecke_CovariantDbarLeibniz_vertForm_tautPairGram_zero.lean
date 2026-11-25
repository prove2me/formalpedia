-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz.vertForm_tautPairGram_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:54:48.756216+00:00
-- url     : https://prove2.me/submissions/0f6c7b17-6bd8-44ab-a181-cd61a688733e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CovariantDbarLeibniz
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CovariantDbarLeibniz_isPosFrame_tautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_eventually_herm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_one
import Theorems.Thm_GlobalTheory_HermFrame_extFormAdj_eq_neg_secondForm
import Theorems.Thm_GlobalTheory_HermFrame_extForm_eq_neg_secondFormAdj
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l k : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
theorem _root_.solution (ξ η : ℂ) :
    vertForm tautPairGram 0 ξ η = kappa * (ξ * conj η) := by
  have hF := isPosFrame_tautPairGram.isHermFrame
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  have hs : subGram (tautPairGram 0) = 1 := by rw [h]; ext a b; simp [subGram, toBlocks₁₁]
  have hq : quotGram (tautPairGram 0) = 1 := by
    rw [h, ← fromBlocks_one, quotGram, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₂₁]; simp
  have hb : ∀ ξ : ℂ, secondForm tautPairGram 0 ξ () () = ξ := fun ξ => by
    rw [secondForm_eq, conn, h, transpose_one, inv_one, Matrix.one_mul]
    change del (fun x : ℂ => x) 0 ξ = ξ
    rw [del_eq_fderiv differentiableAt_fun_id]; simp
  have hu : IsUnit (subGram (tautPairGram 0)).det := by rw [hs]; simp
  rw [vertForm, extFormAdj_eq_neg_secondForm (hF.one trivial) (hF.eventually_herm trivial)
    (hF.isUnit 0 trivial) hu, extForm_eq_neg_secondFormAdj (hF.one trivial)
    (hF.eventually_herm trivial) (hF.isUnit 0 trivial) hu, secondFormAdj, hs, hq, adj]
  simp [hb]
end GlobalTheory.IndefiniteRowSideFullHecke.CovariantDbarLeibniz
