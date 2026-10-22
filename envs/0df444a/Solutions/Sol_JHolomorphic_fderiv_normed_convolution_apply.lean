-- Prove2me | solution 1 for JHolomorphic.fderiv_normed_convolution_apply
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T13:07:37.717947+00:00
-- url     : https://prove2.me/submissions/0a8c8909-03f6-463e-a41d-9d81f9af26a7

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension



namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution

/-- Directional derivatives of a mollified `C¹` function are mollified directional derivatives. -/
theorem fderiv_normed_convolution_apply_aux (ρ : ContDiffBump (0 : ℂ)) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (z v : ℂ) :
    fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] φ) z v =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun x => fderiv ℝ φ x v) z := by
  rw [(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) ρ.integrable_normed.locallyIntegrable hφ z).fderiv]
  have hint : Integrable (fun t => (lsmul ℝ ℝ).precompR ℂ (ρ.normed volume t)
      (fderiv ℝ φ (z - t))) volume := by
    have hcont : Continuous (fun t => (lsmul ℝ ℝ).precompR ℂ (ρ.normed volume t)
        (fderiv ℝ φ (z - t))) := by
      have h1 := hφ.continuous_fderiv one_ne_zero
      exact ((lsmul ℝ ℝ).precompR ℂ).continuous₂.comp
        (ρ.continuous_normed.prodMk (h1.comp (continuous_const.sub continuous_id)))
    refine hcont.integrable_of_hasCompactSupport ?_
    exact (ρ.hasCompactSupport_normed (μ := volume)).mono fun t ht => by
      intro h0; exact ht (by simp [h0])
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hint]
  rfl


/-- A mollification of a bounded continuous function is bounded by three times the bound. -/
theorem norm_normed_convolution_le_aux (ρ : ContDiffBump (0 : ℂ)) {g : ℂ → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (z : ℂ) :
    ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z‖ ≤ 3 * M := by
  have h := ρ.dist_normed_convolution_le (μ := volume) (x₀ := z) (ε := 2 * M)
    hg.aestronglyMeasurable (fun x _ => by
      rw [dist_eq_norm]
      calc ‖g x - g z‖ ≤ ‖g x‖ + ‖g z‖ := norm_sub_le _ _
        _ ≤ 2 * M := by linarith [hM x, hM z])
  calc ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z‖
      ≤ dist ((ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) z) (g z) + ‖g z‖ := by
        rw [dist_eq_norm]; exact norm_le_norm_sub_add _ _
    _ ≤ 2 * M + M := add_le_add h (hM z)
    _ = 3 * M := by ring


/-- The support of a mollification lies in the `rOut`-thickening of the support. -/
theorem tsupport_normed_convolution_subset_aux (ρ : ContDiffBump (0 : ℂ)) (g : ℂ → ℝ) :
    tsupport (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] g) ⊆ cthickening ρ.rOut (tsupport g) := by
  refine (closure_mono ?_).trans (closure_thickening_subset_cthickening _ _)
  refine (support_convolution_subset (lsmul ℝ ℝ)).trans ?_
  rw [ρ.support_normed_eq]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [mem_thickening_iff]
  refine ⟨b, subset_tsupport _ hb, ?_⟩
  rw [mem_ball, dist_zero_right] at ha
  simpa [dist_eq_norm] using ha


/-- Dominated convergence for `∫ Gₙ • w` when the `Gₙ` are uniformly bounded, eventually
supported in a fixed set `K` on which `w` is integrable, and converge pointwise. -/
theorem tendsto_integral_smul_of_bounded_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set ℂ} (hK : MeasurableSet K) {w : ℂ → E} (hw : IntegrableOn w K)
    (G : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (hG : ∀ n, Continuous (G n))
    (hsupp : ∀ᶠ n in atTop, ∀ z ∉ K, G n z = 0) {C : ℝ} (hC : ∀ n z, ‖G n z‖ ≤ C)
    (hlim : ∀ z, Tendsto (fun n => G n z) atTop (𝓝 (g z))) :
    Tendsto (fun n => ∫ z, G n z • w z) atTop (𝓝 (∫ z, g z • w z)) := by
  have hind : ∀ᶠ n in atTop, (fun z => G n z • w z) = K.indicator (fun z => G n z • w z) :=
    hsupp.mono fun n hn => by
      funext z
      by_cases hz : z ∈ K
      · simp [hz]
      · simp [hz, hn z hz]
  refine tendsto_integral_filter_of_dominated_convergence (K.indicator fun z => C * ‖w z‖)
    ?_ ?_ ?_ (Eventually.of_forall fun z => (hlim z).smul_const _)
  · refine hind.mono fun n hn => ?_
    rw [hn, aestronglyMeasurable_indicator_iff hK]
    exact (hG n).aestronglyMeasurable.smul hw.aestronglyMeasurable
  · refine hind.mono fun n hn => Eventually.of_forall fun z => ?_
    have hz' : G n z • w z = K.indicator (fun z => G n z • w z) z := congrFun hn z
    rw [hz']
    by_cases hz : z ∈ K
    · simp only [Set.indicator_of_mem hz, norm_smul]
      exact mul_le_mul_of_nonneg_right (hC n z) (norm_nonneg _)
    · simp [hz]
  · exact IntegrableOn.integrable_indicator
      (Integrable.const_mul (Integrable.norm hw) C) hK

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution

theorem solution (ρ : ContDiffBump (0 : ℂ)) (φ : ℂ → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (z v : ℂ) :
    fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] φ) z v =
      (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun x => fderiv ℝ φ x v) z :=
  fderiv_normed_convolution_apply_aux ρ φ hφ hc z v
