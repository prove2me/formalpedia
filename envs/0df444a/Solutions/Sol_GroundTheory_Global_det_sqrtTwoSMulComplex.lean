-- Prove2me | solution 1 for GroundTheory.Global.det_sqrtTwoSMulComplex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:19.530867+00:00
-- url     : https://prove2.me/submissions/bf99fb1a-ec25-4d15-86ed-bc8ec95db9da

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier

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
theorem _root_.solution : LinearMap.det (sqrtTwoSMulComplex : ℂ →ₗ[ℝ] ℂ) = 2 := by
  have : (sqrtTwoSMulComplex : ℂ →ₗ[ℝ] ℂ) = (√2 : ℝ) • LinearMap.id := LinearMap.ext fun _ => rfl
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex,
    Real.sq_sqrt (by norm_num)]
end GroundTheory.Global
