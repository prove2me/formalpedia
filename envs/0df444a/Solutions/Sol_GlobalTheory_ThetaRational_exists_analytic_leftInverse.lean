-- Prove2me | solution 1 for GlobalTheory.ThetaRational.exists_analytic_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:42:26.904954+00:00
-- url     : https://prove2.me/submissions/b53635aa-435f-485d-a2c9-4e5d880a45af

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
import Theorems.Thm_GlobalTheory_SCV_contDiff_of_differentiable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
namespace GlobalTheory.ThetaRational
theorem _root_.solution {Θ : E → W} (hΘ : Differentiable ℂ Θ) {e : E}
    (hinj : Function.Injective (fderiv ℂ Θ e)) :
    ∃ L : W → E, AnalyticAt ℂ L (Θ e) ∧ ∀ᶠ x in 𝓝 e, L (Θ x) = x := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨P, hP⟩ := (fderiv ℂ Θ e : E →ₗ[ℂ] W).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hinj)
  set P' : W →L[ℂ] E := LinearMap.toContinuousLinearMap P with hP'
  have hd : HasFDerivAt (fun x => P' (Θ x)) ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) e := by
    have := P'.hasFDerivAt.comp e (hΘ e).hasFDerivAt
    refine this.congr_fderiv ?_
    ext v
    have := LinearMap.congr_fun hP v
    simpa [hP'] using this
  have hc : ContDiffAt ℂ ω (fun x => P' (Θ x)) e :=
    (P'.contDiff.comp (GlobalTheory.SCV.contDiff_of_differentiable hΘ ω)).contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨fun y => hc.localInverse hd hn (P' y), ?_, ?_⟩
  · exact AnalyticAt.comp (g := hc.localInverse hd hn) (f := P')
      (hc.to_localInverse hd hn).analyticAt (P'.analyticAt _)
  · exact (hc.hasStrictFDerivAt' hd hn).eventually_left_inverse
end GlobalTheory.ThetaRational
