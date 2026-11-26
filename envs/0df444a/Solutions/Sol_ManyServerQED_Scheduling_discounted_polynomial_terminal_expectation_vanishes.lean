-- Prove2me | solution 1 for ManyServerQED.Scheduling.discounted_polynomial_terminal_expectation_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:21:34.233364+00:00
-- url     : https://prove2.me/submissions/ccada373-5e0e-411a-9ece-3b3eec37e5a6

import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (X : ℝ≥0 → Ω → Fin k → ℝ)
    (hX : ∀ t, Measurable (X t))
    (hMom : ∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ j : ℕ, ∀ t : ℝ≥0,
      Integrable (fun ω => l1norm (X t ω)^p) P ∧
      (∫ ω, l1norm (X t ω)^p ∂P) ≤ c*(1+(t:ℝ)^j))
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f) (γ : ℝ) (hγ : 0 < γ) :
    (∀ T : ℝ≥0, Integrable (fun ω => Real.exp (-γ*(T:ℝ)) * f (X T ω)) P) ∧
    Tendsto (fun T : ℕ => ∫ ω, Real.exp (-γ*(T:ℝ)) * f (X T ω) ∂P) atTop (𝓝 0) := by
  obtain ⟨A,p,hA⟩ := hf.2
  let D := |A|
  have hD (x : Fin k → ℝ) : |f x| ≤ D*(1 + l1norm x^p) :=
    (hA x).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (add_nonneg zero_le_one (pow_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _) : 0 ≤ l1norm x) _)))
  obtain ⟨c,hc,j,hj⟩ := hMom p
  have hm (T : ℝ≥0) : Measurable (fun ω => f (X T ω)) := hf.1.continuous.measurable.comp (hX T)
  have hi (T : ℝ≥0) : Integrable (fun ω => f (X T ω)) P := by
    have hI := ((integrable_const (1:ℝ)).add (hj T).1).const_mul D
    exact hI.mono' (hm T).aestronglyMeasurable (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, Pi.add_apply] using hD (X T ω))
  refine ⟨fun T => (hi T).const_mul _, ?_⟩
  let weight (T : ℝ) := Real.exp (-γ*T)
  let B (T : ℝ) := D*(1+c*(1+T^j))
  have hT0 : Tendsto weight atTop (𝓝 0) := by
    simpa [weight] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 γ hγ
  have hTj : Tendsto (fun t : ℝ => weight t * t^j) atTop (𝓝 0) := by
    simpa only [weight, mul_comm (Real.exp _), Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (j:ℝ) γ hγ
  have hT : Tendsto (fun t : ℝ => weight t * B t) atTop (𝓝 0) := by
    have he : (fun t : ℝ => weight t * B t) =
      fun t => (D*(1+c))*weight t+(D*c)*(weight t*t^j) := by ext t; unfold B; ring
    rw [he]
    simpa using (hT0.const_mul (D*(1+c))).add (hTj.const_mul (D*c))
  refine squeeze_zero_norm' (a := fun n : ℕ => weight n * B n) ?_
    (hT.comp tendsto_natCast_atTop_atTop)
  · apply Eventually.of_forall
    intro T
    let t : ℝ≥0 := T
    have hi' := (hi t).norm
    have hDint := ((integrable_const (1:ℝ)).add (hj t).1).const_mul D
    have hpt : (∫ ω, ‖f (X t ω)‖ ∂P) ≤ D*(1 + ∫ ω, (l1norm (X t ω))^p ∂P) := by
      calc
        _ ≤ ∫ ω, D*(1 + (l1norm (X t ω))^p) ∂P :=
          integral_mono hi' hDint (fun ω => by simpa [Real.norm_eq_abs] using hD (X t ω))
        _ = _ := by rw [integral_const_mul, integral_add (integrable_const _) (hj t).1]; simp
    change ‖∫ ω, weight T * f (X t ω) ∂P‖ ≤ weight T * B T
    rw [integral_const_mul, norm_mul, Real.norm_eq_abs (weight T), abs_of_nonneg (Real.exp_nonneg _)]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (hpt.trans ?_))
      (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_left (add_le_add_right (hj t).2 _) (abs_nonneg A)
