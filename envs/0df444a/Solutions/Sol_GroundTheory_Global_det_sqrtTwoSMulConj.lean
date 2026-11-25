-- Prove2me | solution 1 for GroundTheory.Global.det_sqrtTwoSMulConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:49.300935+00:00
-- url     : https://prove2.me/submissions/442d74a8-7e3b-400d-968e-35f88d186d44

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Theorems.Thm_GroundTheory_Global_det_sqrtTwoSMulComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution : LinearMap.det (sqrtTwoSMulConj : ℂ →ₗ[ℝ] ℂ) = -2 := by
  have : (sqrtTwoSMulConj : ℂ →ₗ[ℝ] ℂ) =
      (sqrtTwoSMulComplex : ℂ →ₗ[ℝ] ℂ) ∘ₗ Complex.conjAe.toLinearEquiv.toLinearMap :=
    LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_comp, det_sqrtTwoSMulComplex, Complex.det_conjAe]
  norm_num
end GroundTheory.Global
