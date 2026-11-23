-- Prove2me | solution 1 for Kyprianou.Ch02.finiteDiracMarkIntegralTendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:59:29.383028+00:00
-- url     : https://prove2.me/submissions/97fbb113-d17b-46bd-8286-50e2419863f8

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Pointwise convergence may be integrated over a finite weighted Dirac measure. -/
theorem solution
    (μ : Measure (ℝ × ℝ))
    (s : Finset (ℝ × ℝ)) (c : ℝ × ℝ → ℝ≥0∞)
    (hc : ∀ p ∈ s, c p ≠ ⊤)
    (hμ : μ = ∑ p ∈ s, c p • Measure.dirac p)
    (f : ℕ → ℝ → ℝ)
    (hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x)) :
    Tendsto (fun n => ∫ z : ℝ × ℝ, f n z.2 ∂μ)
      atTop (𝓝 (∫ z : ℝ × ℝ, z.2 ∂μ)) := by
  classical
  have hfi (n : ℕ) (p : ℝ × ℝ) (hp : p ∈ s) :
      Integrable (fun z : ℝ × ℝ => f n z.2)
        (c p • Measure.dirac p) := by
    by_cases hz : c p = 0
    · simp [hz]
    · exact (integrable_smul_measure hz (hc p hp)).2
        (integrable_dirac (by simp))
  have hgi (p : ℝ × ℝ) (hp : p ∈ s) :
      Integrable (fun z : ℝ × ℝ => z.2)
        (c p • Measure.dirac p) := by
    by_cases hz : c p = 0
    · simp [hz]
    · exact (integrable_smul_measure hz (hc p hp)).2
        (integrable_dirac (by simp))
  have hfn (n : ℕ) :
      (∫ z : ℝ × ℝ, f n z.2 ∂μ) =
        ∑ p ∈ s, (c p).toReal * f n p.2 := by
    rw [hμ, integral_finset_sum_measure (fun p hp => hfi n p hp)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [integral_smul_measure, integral_dirac]
    simp only [smul_eq_mul]
  have hg :
      (∫ z : ℝ × ℝ, z.2 ∂μ) =
        ∑ p ∈ s, (c p).toReal * p.2 := by
    rw [hμ, integral_finset_sum_measure hgi]
    apply Finset.sum_congr rfl
    intro p hp
    rw [integral_smul_measure, integral_dirac]
    simp only [smul_eq_mul]
  have hsum : Tendsto
      (fun n : ℕ => ∑ p ∈ s, (c p).toReal * f n p.2)
      atTop (𝓝 (∑ p ∈ s, (c p).toReal * p.2)) := by
    apply tendsto_finset_sum
    intro p hp
    exact (hf p.2).const_mul (c p).toReal
  have heq : (fun n : ℕ => ∫ z : ℝ × ℝ, f n z.2 ∂μ) =
      (fun n : ℕ => ∑ p ∈ s, (c p).toReal * f n p.2) := by
    funext n
    exact hfn n
  rw [heq, hg]
  exact hsum
