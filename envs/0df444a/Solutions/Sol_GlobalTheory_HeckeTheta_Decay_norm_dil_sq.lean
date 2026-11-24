-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.norm_dil_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:45.182829+00:00
-- url     : https://prove2.me/submissions/5c402364-73ce-4437-bec8-a89e86af4b7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeTheta.Decay
theorem _root_.solution (y : I → ℝ) (v : I → ℂ) (i : I) :
    ‖dil y v i‖ ^ 2 = Real.exp (y i) * ‖v i‖ ^ 2 := by
  unfold dil
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have : Real.exp (y i / 2) ^ 2 = Real.exp (y i) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this]
end GlobalTheory.HeckeTheta.Decay
