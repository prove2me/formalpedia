-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.curv_tautPairGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:08.645713+00:00
-- url     : https://prove2.me/submissions/b019659f-e060-4d17-95f2-ceb3ad22f8ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_tautPairGram_eq
import Theorems.Thm_GlobalTheory_HermFrame_Model_mContDiffAt_pairFrame
import Theorems.Thm_GlobalTheory_HermFrame_Model_det_pairFrame
import Theorems.Thm_GlobalTheory_HermFrame_curv_changeFrame
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
theorem _root_.solution (z ξ η : ℂ) : curv tautPairGram z ξ η = 0 := by
  rw [funext tautPairGram_eq, curv_changeFrame (mContDiffAt_const 1) (by simp)
    (mContDiffAt_pairFrame 2 z) (by simp [det_pairFrame])
    (Eventually.of_forall fun x η => ?_)]
  · simp
  · ext (a | a) (b | b) <;> simp only [mdbar_apply, pairFrame, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;>
      rw [dbar_eq_zero (by fun_prop)] <;> rfl
end GlobalTheory.HermFrame.Model
