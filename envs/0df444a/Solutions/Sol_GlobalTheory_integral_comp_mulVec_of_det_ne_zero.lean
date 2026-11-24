-- Prove2me | solution 1 for GlobalTheory.integral_comp_mulVec_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:49.388599+00:00
-- url     : https://prove2.me/submissions/3ab645cf-3765-4206-b257-dfaf5615baa1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {P : Matrix ι ι ℝ} (hP : P.det ≠ 0)
    {f : (ι → ℝ) → ℂ} (hf : Continuous f) :
    ∫ x, f (P *ᵥ x) = (|P.det⁻¹| : ℝ) * ∫ y, f y := by
  have h := integral_map (μ := (volume : Measure (ι → ℝ))) (φ := toLin' P) (f := f)
    (toLin' P).continuous_of_finiteDimensional.measurable.aemeasurable hf.aestronglyMeasurable
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hP, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), real_smul] at h
  rw [h]
  rfl
end GlobalTheory
