-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.curv_sub_quot_tautPairGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:02.617218+00:00
-- url     : https://prove2.me/submissions/97a47d22-477e-4815-9654-d24714e7f780

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_curv_sub
import Theorems.Thm_GlobalTheory_HermFrame_Model_curv_quot
import Theorems.Thm_GlobalTheory_HermFrame_Model_isPosFrame_tautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_curv_tautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_secondForm_tautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_secondFormAdj_tautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_eventually_herm
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_one
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_sub
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_two
import Theorems.Thm_GlobalTheory_HermFrame_IsPosFrame_sub
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
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.HermFrame.Model
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
namespace GlobalTheory.HermFrame.Model
theorem _root_.solution (ξ η : ℂ) :
    curv (fun x => subGram (tautPairGram x)) 0 ξ η () () = -(ξ * conj η) ∧
    curv (fun x => quotGram (tautPairGram x)) 0 ξ η () () = ξ * conj η ∧
    extTrace tautPairGram 0 ξ η = kappa * (ξ * conj η) := by
  have h := isPosFrame_tautPairGram.isHermFrame
  have hs := isPosFrame_tautPairGram.sub.isHermFrame.isUnit 0 trivial
  have a := h.two (z := 0) trivial
  have b := h.eventually_herm (z := 0) trivial
  have c := h.isUnit 0 trivial
  rw [curv_sub a b c hs, curv_quot a b c hs, extTrace,
    extFormAdj_eq_neg_secondForm (h.one trivial) b c hs,
    extForm_eq_neg_secondFormAdj (h.one trivial) b c hs, curv_tautPairGram,
    secondForm_tautPairGram, secondFormAdj_tautPairGram]
  simp [blockSS, blockQQ, mul_apply, trace, mul_comm]
end GlobalTheory.HermFrame.Model
