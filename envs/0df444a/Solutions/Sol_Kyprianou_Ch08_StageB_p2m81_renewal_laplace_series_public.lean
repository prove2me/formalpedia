-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_renewal_laplace_series_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T05:45:46.698271+00:00
-- url     : https://prove2.me/submissions/376ff9e9-dbbb-4da1-91c0-f20446de048c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_lintegral_conv
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
theorem solution
    (ρ : Measure ℝ) (hprob : IsProbabilityMeasure ρ)
    (κ : Measure ℝ) [SFinite κ]
    (m : ℕ → Measure ℝ) (hm0 : m 0 = Measure.dirac 0)
    (hmsucc : ∀ n : ℕ, m (n + 1) = κ.conv (m n))
    (hsf : ∀ n : ℕ, SFinite (m n))
    (c : ℝ≥0∞) (ν : Measure ℝ)
    (hν : ν = Measure.sum (fun n : ℕ => c • (ρ.conv (m n))))
    (hκlt : ∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) < 1) :
    ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
        c * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) *
          (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ))⁻¹ := by
  intro s hs
  have hmul : ∀ a b : Measure ℝ, a ∗ b = a.conv b := fun a b => rfl
  have hmn : ∀ n : ℕ, (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(m n)) =
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) ^ n := by
    intro n
    induction n with
    | zero =>
      rw [hm0]
      simp [lintegral_dirac]
    | succ n ih =>
      haveI := hsf n
      rw [hmsucc n, ← hmul, AvramDividend.Classical.positiveLaplace_lintegral_conv, ih,
        pow_succ']
  have hconv : ∀ n : ℕ, (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρ.conv (m n))) =
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) *
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) ^ n := by
    intro n
    haveI := hsf n
    rw [← hmul, AvramDividend.Classical.positiveLaplace_lintegral_conv, hmn n]
  rw [hν, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul, hconv, ← mul_assoc,
    ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
