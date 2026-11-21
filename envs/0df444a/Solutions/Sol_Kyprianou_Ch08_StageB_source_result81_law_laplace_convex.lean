-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_law_laplace_convex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T14:08:42.046664+00:00
-- url     : https://prove2.me/submissions/d441e0b6-abac-457e-b7da-66b2e39c58e4

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem holder_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (Z : Ω → ℝ) (hZ : AEMeasurable Z P) (x y a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx : Integrable (fun ω => Real.exp (x * Z ω)) P)
    (hy : Integrable (fun ω => Real.exp (y * Z ω)) P) :
    ∫ ω, Real.exp ((a * x + b * y) * Z ω) ∂P ≤
      (∫ ω, Real.exp (x * Z ω) ∂P) ^ a * (∫ ω, Real.exp (y * Z ω) ∂P) ^ b := by
  have hpq : (a⁻¹).HolderConjugate (b⁻¹) := Real.HolderConjugate.inv_inv ha hb hab
  have hpow : ∀ (c u : ℝ), 0 < c → ∀ ω, (Real.exp (c * u * Z ω)) ^ c⁻¹ = Real.exp (u * Z ω) := by
    intro c u hc ω
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hmem : ∀ (c u : ℝ), 0 < c → Integrable (fun ω => Real.exp (u * Z ω)) P →
      MemLp (fun ω => Real.exp (c * u * Z ω)) (ENNReal.ofReal c⁻¹) P := by
    intro c u hc hu
    have hm : AEStronglyMeasurable (fun ω => Real.exp (c * u * Z ω)) P :=
      (Real.measurable_exp.comp_aemeasurable (aemeasurable_const.mul hZ)).aestronglyMeasurable
    rw [← integrable_norm_rpow_iff hm (by simp [hc]) (by simp), ENNReal.toReal_ofReal (inv_nonneg.2 hc.le)]
    refine hu.congr (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (hpow c u hc ω).symm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun ω => (Real.exp_pos (a * x * Z ω)).le)
    (Eventually.of_forall fun ω => (Real.exp_pos (b * y * Z ω)).le)
    (hmem a x ha hx) (hmem b y hb hy)
  simp only [hpow a x ha, hpow b y hb, one_div, inv_inv] at h
  calc ∫ ω, Real.exp ((a * x + b * y) * Z ω) ∂P
      = ∫ ω, Real.exp (a * x * Z ω) * Real.exp (b * y * Z ω) ∂P := by
        congr 1
        ext ω
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ _ := h

private theorem convex_of_exponential_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (Z : Ω → ℝ)
    (hZ : AEMeasurable Z P) (ψ : ℝ → ℝ)
    (hm : ∀ θ : ℝ, 0 ≤ θ → Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hexp : ∀ θ : ℝ, 0 ≤ θ →
      (∫ ω, Real.exp (θ * Z ω) ∂P) = Real.exp (ψ θ)) :
    ConvexOn ℝ (Ici 0) ψ := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_Ici] at hx hy
  simp only [smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst b
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · have : a = 1 := by linarith
    subst a
    simp
  have h := holder_moments Z hZ x y a b ha' hb' hab (hm x hx) (hm y hy)
  have hxy : 0 ≤ a * x + b * y := by positivity
  rw [hexp _ hxy, hexp _ hx, hexp _ hy, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add] at h
  linarith [Real.exp_le_exp.1 h]

private theorem one_time_moment_exp
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * D.X 1 ω) ∂P) = Real.exp (ψ θ) := by
  have hs : Function.support (fun ω => Real.exp (θ * D.X 1 ω)) = univ := by
    ext ω
    simp [Function.mem_support]
  have hp : 0 < ∫ ω, Real.exp (θ * D.X 1 ω) ∂P := by
    apply (integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos _).le) ((hψ θ 1 hθ zero_lt_one).1)).2
    change 0 < P (Function.support (fun ω => Real.exp (θ * D.X 1 ω)))
    rw [hs, measure_univ]
    exact zero_lt_one
  have hlog : ψ θ = Real.log (∫ ω, Real.exp (θ * D.X 1 ω) ∂P) := by
    simpa [SpectrallyNegativeModel.toData] using (hψ θ 1 hθ zero_lt_one).2
  rw [hlog, Real.exp_log hp]

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ConvexOn ℝ (Ici 0) ψ := by
  have hZ : AEMeasurable (D.X 1) P := by
    have hi := (D.levy.stationary_increments 0 1).aemeasurable_snd
    change AEMeasurable (fun ω => D.X 1 ω - D.X 0 ω) P at hi
    simpa only [D.levy.start_zero, sub_zero] using hi
  exact convex_of_exponential_moments (D.X 1) hZ ψ
    (fun θ hθ => (hψ θ 1 hθ zero_lt_one).1)
    (one_time_moment_exp Ω P D ψ hψ)
