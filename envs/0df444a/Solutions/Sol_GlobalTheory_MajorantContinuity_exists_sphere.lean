-- Prove2me | solution 1 for GlobalTheory.MajorantContinuity.exists_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:35.944607+00:00
-- url     : https://prove2.me/submissions/9dad506f-8a64-4d0b-948e-9f7e8e1c5e31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder
open GlobalTheory GlobalTheory.MajorantContinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajorantContinuity
theorem _root_.solution {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) :
    ∃ w ∈ Metric.sphere (0 : Fin r → ℂ) 1, v = ((‖v‖ : ℝ) : ℂ) • w := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  refine ⟨((‖v‖ : ℝ) : ℂ)⁻¹ • v, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, inv_mul_cancel₀ hn]
  · rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hn), one_smul]
end GlobalTheory.MajorantContinuity
