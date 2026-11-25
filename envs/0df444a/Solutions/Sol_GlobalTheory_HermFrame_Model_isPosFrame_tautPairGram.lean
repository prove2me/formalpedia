-- Prove2me | solution 1 for GlobalTheory.HermFrame.Model.isPosFrame_tautPairGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:31.95826+00:00
-- url     : https://prove2.me/submissions/ebf8d7f7-cd28-461e-9d71-d118b86e8970

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CurvSubQuotTautPairGram
import Theorems.Thm_GlobalTheory_HermFrame_Model_tautPairGram_eq
import Theorems.Thm_GlobalTheory_HermFrame_Model_mContDiffAt_pairFrame
import Theorems.Thm_GlobalTheory_HermFrame_Model_det_pairFrame
import Theorems.Thm_GlobalTheory_HermFrame_MContDiffAt_conjTranspose
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
theorem _root_.solution : IsPosFrame Set.univ tautPairGram := by
  refine ⟨isOpen_univ, fun a b z _ => ?_, fun z _ => ?_⟩
  · simp only [funext tautPairGram_eq]
    exact ((((mContDiffAt_pairFrame ∞ z).transpose.mul (mContDiffAt_const 1)).mul
      (mContDiffAt_pairFrame ∞ z).conjTranspose.transpose) a b).contDiffWithinAt
  · rw [tautPairGram_eq, ← PosDef.transpose_iff]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_one]
    exact PosDef.conjTranspose_mul_self _ (mulVec_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (by simp [det_pairFrame])))
end GlobalTheory.HermFrame.Model
