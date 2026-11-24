-- Prove2me | solution 1 for GlobalTheory.MatrixGaussian.map_mulVec_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:54:39.099156+00:00
-- url     : https://prove2.me/submissions/ca8b07dc-cd75-441c-95d5-af217d4e4882

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.MatrixGaussian
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.MatrixGaussian
theorem _root_.solution (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    Measure.map (fun z : ι → ℂ => M *ᵥ z) volume = ENNReal.ofReal (normSq M.det)⁻¹ • volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = normSq M.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; simpa using hM)
  rw [hdet, abs_of_nonneg (inv_nonneg.2 (normSq_nonneg _))] at this
  exact this
end GlobalTheory.MatrixGaussian
