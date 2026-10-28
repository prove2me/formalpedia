-- Prove2me | solution 1 for HuImkellerMuller.Power.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:56:48.370282+00:00
-- url     : https://prove2.me/submissions/d95c754e-6c4a-4aa1-a523-edb979c87645

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

open HuImkellerMuller.Power in
theorem solution {m : ℕ} (C : Set (EuclideanSpace ℝ (Fin m))) (hC : IsClosed C)
    (θ z : EuclideanSpace ℝ (Fin m)) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ ρ ∈ C, γ * inner ℝ ρ θ - (1 / 2) * γ * ‖ρ‖ ^ 2 + powerDriver θ C γ z
        ≤ -(1 / 2) * ‖γ • ρ + z‖ ^ 2) ∧
    (∀ ρ ∈ HuImkellerMuller.Exponential.proj C ((1 / (1 - γ)) • (z + θ)),
        γ * inner ℝ ρ θ - (1 / 2) * γ * ‖ρ‖ ^ 2 + powerDriver θ C γ z
          = -(1 / 2) * ‖γ • ρ + z‖ ^ 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (1 - γ) := ⟨_, rfl⟩
  have hne : (1 - γ) ≠ 0 := by linarith
  have hc' : (1 - γ) * c = 1 := by rw [hc]; exact mul_one_div_cancel hne
  have main : ∀ ρ : EuclideanSpace ℝ (Fin m),
      γ * inner ℝ ρ θ - (1 / 2) * γ * ‖ρ‖ ^ 2 + powerDriver θ C γ z + (1 / 2) * ‖γ • ρ + z‖ ^ 2
        = γ * (1 - γ) / 2 * (Metric.infDist (c • (z + θ)) C ^ 2 - ‖c • (z + θ) - ρ‖ ^ 2) := by
    intro ρ
    have h1 : ‖γ • ρ + z‖ ^ 2 = γ ^ 2 * ‖ρ‖ ^ 2 + 2 * γ * inner ℝ ρ z + ‖z‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have hin : inner ℝ (z + θ) ρ = inner ℝ ρ z + inner ℝ ρ θ := by
      rw [real_inner_comm, inner_add_right]
    have h2 : ‖c • (z + θ) - ρ‖ ^ 2 =
        c ^ 2 * ‖z + θ‖ ^ 2 - 2 * c * (inner ℝ ρ z + inner ℝ ρ θ) + ‖ρ‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, hin, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have hk : γ * ‖z + θ‖ ^ 2 / (2 * (1 - γ)) = γ * ‖z + θ‖ ^ 2 / 2 * c := by
      rw [hc, div_mul_div_comm, mul_one]
    unfold powerDriver
    rw [← hc]
    linear_combination (1 / 2) * h1 + (γ * (1 - γ) / 2) * h2
      + (-γ * (inner ℝ ρ z + inner ℝ ρ θ) + γ * ‖z + θ‖ ^ 2 / 2 * c) * hc'
      - hk
  have hcoef : 0 ≤ γ * (1 - γ) / 2 := by
    have : 0 ≤ 1 - γ := by linarith
    positivity
  refine ⟨fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · have hD0 : 0 ≤ Metric.infDist (c • (z + θ)) C := Metric.infDist_nonneg
    have hD1 : Metric.infDist (c • (z + θ)) C ≤ ‖c • (z + θ) - ρ‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hρ
    have hsq : Metric.infDist (c • (z + θ)) C ^ 2 ≤ ‖c • (z + θ) - ρ‖ ^ 2 :=
      pow_le_pow_left₀ hD0 hD1 2
    have := mul_nonpos_of_nonneg_of_nonpos hcoef (sub_nonpos.mpr hsq)
    linarith [main ρ]
  · obtain ⟨_, hρ2⟩ := hρ
    rw [← hc] at hρ2
    have := main ρ
    rw [← hρ2, sub_self, mul_zero] at this
    linarith
