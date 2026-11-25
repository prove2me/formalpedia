-- Prove2me | solution 1 for GlobalTheory.JacobianIndependence.eq_zero_of_det_fderiv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:57:40.49358+00:00
-- url     : https://prove2.me/submissions/295a0135-1125-4e24-97ce-09a42dd41d7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfDetFderivNeZero
import Theorems.Thm_GlobalTheory_JacobianIndependence_eq_zero_of_eventually_eval
import Theorems.Thm_GlobalTheory_SCV_analyticAt_iff_eventually_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open Filter Topology
open GlobalTheory GlobalTheory.JacobianIndependence
namespace GlobalTheory.JacobianIndependence
theorem _root_.solution :
    ∀ (n : ℕ) (f : Fin n → V n → ℂ), (∀ k, ∀ᶠ z in nhds (0 : V n), DifferentiableAt ℂ (f k) z) →
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => f k z : V n)) 0).det ≠ 0 →
      ∀ p : MvPolynomial (Fin n) ℂ,
        (∀ᶠ z in nhds (0 : V n), MvPolynomial.eval (fun k => f k z) p = 0) → p = 0 := by
  intro n f hf hdet p hp
  set F : V n → V n := fun z : V n => (WithLp.toLp 2 fun k => f k z : V n) with hF
  have hd : ∀ᶠ z in 𝓝 (0 : V n), DifferentiableAt ℂ F z := by
    filter_upwards [Filter.eventually_all.2 hf] with z hz
    exact differentiableAt_euclidean.2 hz
  have ha : AnalyticAt ℂ F 0 := GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hd
  have hs : HasStrictFDerivAt F
      (((fderiv ℂ F 0).toContinuousLinearEquivOfDetNeZero hdet : V n ≃L[ℂ] V n) :
        V n →L[ℂ] V n) 0 := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact ha.hasStrictFDerivAt
  refine eq_zero_of_eventually_eval p (F 0) ?_
  rw [← hs.map_nhds_eq_of_equiv, Filter.eventually_map]
  exact hp
end GlobalTheory.JacobianIndependence
