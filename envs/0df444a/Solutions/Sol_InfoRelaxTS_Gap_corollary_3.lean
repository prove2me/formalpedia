-- Prove2me | solution 1 for InfoRelaxTS.Gap.corollary_3
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T18:03:45.381231+00:00
-- url     : https://prove2.me/submissions/20d36bf1-78d5-438b-8f5b-50327d526afa

import Mathlib

open MeasureTheory ProbabilityTheory

namespace Prove2InfoRelaxSubmission

namespace InfoRelaxTS.Gap

theorem corollary_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hX : HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) ⟨σ ^ 2, sq_nonneg σ⟩ μ) :
    (∀ z : ℝ, 0 ≤ z →
      (μ {ω | (∫ x, X x ∂μ) + z * σ ≤ X ω}).toReal ≤ Real.exp (-z ^ 2 / 2)) ∧
    (∀ z : ℝ, 0 < z →
      ∫ ω, max (X ω - ((∫ x, X x ∂μ) + z * σ)) 0 ∂μ ≤ σ / z * Real.exp (-z ^ 2 / 2)) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · -- (209): sub-Gaussian Chernoff bound at `ε = z σ`.
    have hset : {ω | (∫ x, X x ∂μ) + z * σ ≤ X ω} = {ω | z * σ ≤ X ω - ∫ x, X x ∂μ} := by
      ext ω
      constructor
      · intro h
        have h' : (∫ x, X x ∂μ) + z * σ ≤ X ω := h
        show z * σ ≤ X ω - ∫ x, X x ∂μ
        linarith
      · intro h
        have h' : z * σ ≤ X ω - ∫ x, X x ∂μ := h
        show (∫ x, X x ∂μ) + z * σ ≤ X ω
        linarith
    have hb := hX.measure_ge_le (ε := z * σ) (mul_nonneg hz hσ.le)
    have he : Real.exp (-(z * σ) ^ 2 / (2 * ((⟨σ ^ 2, sq_nonneg σ⟩ : NNReal) : ℝ)))
        = Real.exp (-z ^ 2 / 2) := by
      congr 1
      change -(z * σ) ^ 2 / (2 * σ ^ 2) = -z ^ 2 / 2
      rw [div_eq_div_iff (mul_pos two_pos (pow_pos hσ 2)).ne' two_ne_zero]
      ring
    rw [hset]
    calc (μ {ω | z * σ ≤ X ω - ∫ x, X x ∂μ}).toReal
        = μ.real {ω | z * σ ≤ X ω - ∫ x, X x ∂μ} := rfl
      _ ≤ _ := hb
      _ = Real.exp (-z ^ 2 / 2) := he
  · -- (210): `λ x₊ ≤ exp (λ x - 1)` with `λ = z / σ`, then the sub-Gaussian MGF bound.
    have hl : 0 < z / σ := div_pos hz hσ
    have hint : Integrable (fun ω => Real.exp (z / σ * (X ω - ∫ x, X x ∂μ))
        * Real.exp (-(z / σ * (z * σ)) - 1)) μ :=
      (hX.integrable_exp_mul (z / σ)).mul_const _
    have hpt : ∀ ω, z / σ * max (X ω - ((∫ x, X x ∂μ) + z * σ)) 0
        ≤ Real.exp (z / σ * (X ω - ∫ x, X x ∂μ)) * Real.exp (-(z / σ * (z * σ)) - 1) := by
      intro ω
      rw [← Real.exp_add, mul_max_of_nonneg _ _ hl.le, mul_zero]
      refine max_le ?_ (Real.exp_pos _).le
      have h1 := Real.add_one_le_exp (z / σ * (X ω - ((∫ x, X x ∂μ) + z * σ)) - 1)
      have e : z / σ * (X ω - ∫ x, X x ∂μ) + (-(z / σ * (z * σ)) - 1)
          = z / σ * (X ω - ((∫ x, X x ∂μ) + z * σ)) - 1 := by ring
      rw [e]
      linarith
    have hmono : ∫ ω, z / σ * max (X ω - ((∫ x, X x ∂μ) + z * σ)) 0 ∂μ
        ≤ ∫ ω, Real.exp (z / σ * (X ω - ∫ x, X x ∂μ)) * Real.exp (-(z / σ * (z * σ)) - 1) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => mul_nonneg hl.le (le_max_right _ _)) hint
        (ae_of_all _ hpt)
    rw [integral_const_mul, integral_mul_const] at hmono
    have hm2 : (∫ ω, Real.exp (z / σ * (X ω - ∫ x, X x ∂μ)) ∂μ)
        ≤ Real.exp (σ ^ 2 * (z / σ) ^ 2 / 2) := by
      have h2 := hX.mgf_le (z / σ)
      change (∫ ω, Real.exp (z / σ * (X ω - ∫ x, X x ∂μ)) ∂μ)
        ≤ Real.exp (σ ^ 2 * (z / σ) ^ 2 / 2) at h2
      exact h2
    have hexp : Real.exp (σ ^ 2 * (z / σ) ^ 2 / 2) * Real.exp (-(z / σ * (z * σ)) - 1)
        ≤ Real.exp (-z ^ 2 / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e1 : σ ^ 2 * (z / σ) ^ 2 = z ^ 2 := by
        calc σ ^ 2 * (z / σ) ^ 2 = z ^ 2 * (σ / σ) ^ 2 := by ring
          _ = z ^ 2 := by rw [div_self hσ.ne']; ring
      have e2 : z / σ * (z * σ) = z ^ 2 := by
        calc z / σ * (z * σ) = z ^ 2 * (σ / σ) := by ring
          _ = z ^ 2 := by rw [div_self hσ.ne']; ring
      rw [e1, e2]
      linarith
    have hfinal : z / σ * ∫ ω, max (X ω - ((∫ x, X x ∂μ) + z * σ)) 0 ∂μ
        ≤ Real.exp (-z ^ 2 / 2) :=
      hmono.trans ((mul_le_mul_of_nonneg_right hm2 (Real.exp_pos _).le).trans hexp)
    have hgoal : σ / z * Real.exp (-z ^ 2 / 2) = Real.exp (-z ^ 2 / 2) / (z / σ) := by
      rw [div_div_eq_mul_div]
      ring
    rw [hgoal, le_div_iff₀ hl]
    linarith [hfinal]

end InfoRelaxTS.Gap

end Prove2InfoRelaxSubmission

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hX : HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) ⟨σ ^ 2, sq_nonneg σ⟩ μ) :
    (∀ z : ℝ, 0 ≤ z →
      (μ {ω | (∫ x, X x ∂μ) + z * σ ≤ X ω}).toReal ≤ Real.exp (-z ^ 2 / 2)) ∧
    (∀ z : ℝ, 0 < z →
      ∫ ω, max (X ω - ((∫ x, X x ∂μ) + z * σ)) 0 ∂μ ≤ σ / z * Real.exp (-z ^ 2 / 2)) := by
  exact _root_.Prove2InfoRelaxSubmission.InfoRelaxTS.Gap.corollary_3 μ X σ hσ hX
