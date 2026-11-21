-- Prove2me | solution 1 for LevyStochCalc.Examples.Nonvacuity.lintegral_nnnorm_sq_brownian
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T05:31:56.99161+00:00
-- url     : https://prove2.me/submissions/f1fedbb4-b3cb-414c-94c7-d145051171f4

import Definitions.Def_LevyStochCalc_Brownian_Construction_F000

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖W.W t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal t := by
  have hcongr : (fun ω => W.W t ω) =ᵐ[P] (fun ω => W.W t ω - W.W 0 ω) := by
    filter_upwards [W.initial_zero] with ω h
    simp [h]
  have hmap : P.map (W.W t) = gaussianReal (0 : ℝ) ⟨t, le_of_lt ht⟩ := by
    calc P.map (W.W t) = P.map (fun ω => W.W t ω - W.W 0 ω) := Measure.map_congr hcongr
      _ = gaussianReal 0 ⟨t - 0, by linarith⟩ := W.increment_gaussian le_rfl ht
      _ = gaussianReal 0 ⟨t, le_of_lt ht⟩ := by norm_num
  have hsq : ∀ x : ℝ, ((‖x‖₊ : ℝ≥0∞) ^ 2) = ENNReal.ofReal (x ^ 2) := by
    intro x
    have h1 : (↑‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
      rw [ENNReal.coe_nnreal_eq]
      first | rfl | simp | norm_num
    rw [h1, ← ENNReal.ofReal_pow (norm_nonneg x) 2, Real.norm_eq_abs, sq_abs]
  have hgauss : ∫ x, x ^ 2 ∂(gaussianReal (0 : ℝ) ⟨t, le_of_lt ht⟩) = t := by
    haveI : IsProbabilityMeasure (gaussianReal (0 : ℝ) ⟨t, le_of_lt ht⟩) :=
      instIsProbabilityMeasureGaussianReal 0 ⟨t, le_of_lt ht⟩
    have hmem : MemLp id 2 (gaussianReal (0 : ℝ) ⟨t, le_of_lt ht⟩) :=
      memLp_id_gaussianReal 2
    have h := variance_id_gaussianReal (μ := (0 : ℝ)) (v := ⟨t, le_of_lt ht⟩)
    rw [variance_eq_sub hmem] at h
    simp at h
    have hB : ∫ (x : ℝ), x ∂gaussianReal (0 : ℝ) ⟨t, le_of_lt ht⟩ = 0 := integral_id_gaussianReal
    have hval : ((⟨t, le_of_lt ht⟩ : ℝ≥0) : ℝ) = t := rfl
    have key : ∀ A B c : ℝ, A - B ^ 2 = c → B = 0 → c = t → A = t := by
      intro A B c h1 h2 h3
      rw [h2] at h1
      norm_num at h1
      linarith
    exact key _ _ _ h hB hval
  rw [← MeasureTheory.lintegral_map (f := fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) (g := W.W t)
    (by fun_prop) (W.measurable_eval t)]
  rw [hmap]
  simp only [hsq]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (show Integrable (fun x : ℝ => x ^ 2) (gaussianReal (0 : ℝ) ⟨t, le_of_lt ht⟩) from
      (memLp_id_gaussianReal 2).integrable_sq)
    (by filter_upwards with x using sq_nonneg x)]
  rw [hgauss]
