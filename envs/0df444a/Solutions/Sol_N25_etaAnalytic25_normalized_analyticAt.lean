-- Prove2me | solution 1 for N25.etaAnalytic25_normalized_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:53.364252+00:00
-- url     : https://prove2.me/submissions/428490ae-adc6-49ba-ae6d-40da90604553

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_etaAnalytic25_normalized_hasSum

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Filter Topology Function Complex UpperHalfPlane

namespace N25

private theorem cusp_hasSum_punctured {f : UpperHalfPlane → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : UpperHalfPlane,
      HasSum (fun m => c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ))
    {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasSum (fun m => c m • q ^ m) (UpperHalfPlane.cuspFunction 1 f q) := by
  have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one zero_lt_one hq hq0
  let τ : UpperHalfPlane := ⟨Function.Periodic.invQParam 1 q, h1⟩
  have h2 := Function.Periodic.cuspFunction_eq_of_nonzero 1 (f ∘ UpperHalfPlane.ofComplex) hq0
  have he : UpperHalfPlane.cuspFunction 1 f q = f τ := by
    simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h1] using! h2
  grind [hf τ, Function.Periodic.qParam_right_inv]

private theorem cusp_updated_powerSeries {f : UpperHalfPlane → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : UpperHalfPlane,
      HasSum (fun m => c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ)) :
    HasFPowerSeriesOnBall (Function.update (UpperHalfPlane.cuspFunction 1 f) 0 (c 0))
      (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      let : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [smul_eq_mul, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
        (cusp_hasSum_punctured hf (q := r) (by simpa using hr) (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm] using cusp_hasSum_punctured hf hy hy'

private theorem analytic_cusp_of_hasSum {f : UpperHalfPlane → ℂ} {c : ℕ → ℂ}
    (hf : ∀ τ : UpperHalfPlane,
      HasSum (fun m => c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ)) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0 := by
  have H := cusp_updated_powerSeries hf
  have ht : Tendsto (UpperHalfPlane.cuspFunction 1 f) (𝓝[≠] (0 : ℂ)) (𝓝 (c 0)) := by
    have h := H.hasFPowerSeriesAt.continuousAt.tendsto.mono_left
      (show (𝓝[≠] (0 : ℂ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simp only [update_self] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact Function.update_of_ne hq _ _
  have hv : UpperHalfPlane.cuspFunction 1 f 0 = c 0 := by
    rw [UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    exact ht.limUnder_eq
  have he : Function.update (UpperHalfPlane.cuspFunction 1 f) 0 (c 0) =
      UpperHalfPlane.cuspFunction 1 f := Function.update_eq_self_iff.mpr hv.symm
  rw [he] at H
  exact H.hasFPowerSeriesAt.analyticAt

/-- The normalized eta residue series gives the actual analytic extension at the q-origin. -/
theorem _root_.solution
    (g : ℕ) (hg : 0 < g) (hg25 : g < 25) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1
      (fun τ : UpperHalfPlane => etaAnalytic25 g τ / Complex.exp (Real.pi * Complex.I *
        (((g : ℂ) / 25) ^ 2 - (g : ℂ) / 25 + 1 / 6) * (25 * (τ : ℂ))))) 0 := by
  apply analytic_cusp_of_hasSum (c := fun n =>
    ((PowerSeries.coeff n (etaResidueSeries25 g) : ℤ) : ℂ))
  intro τ
  simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one, smul_eq_mul] using
    etaAnalytic25_normalized_hasSum g hg hg25 τ

end N25
