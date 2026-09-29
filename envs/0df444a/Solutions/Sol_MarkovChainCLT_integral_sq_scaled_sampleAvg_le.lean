-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_scaled_sampleAvg_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:29:17.102014+00:00
-- url     : https://prove2.me/submissions/0cb51cbd-5fb9-408f-860a-1625684305a5

import Theorems.Thm_MarkovChainCLT_integral_sq_sum_coord_le_of_sq_integrable
import Theorems.Thm_ProbabilityTheory_integrable_of_integrable_sq
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (N : ℕ) (hN : 1 ≤ N) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16)
    (r : X → ℝ) (hr : Measurable r) (hL2 : Integrable (fun x => (r x) ^ 2) π) (n : ℕ) :
    ∫ ω, (Real.sqrt n * (sampleAvg r n ω - ∫ x, r x ∂π)) ^ 2 ∂(chainMeasure P π)
      ≤ 4 * N * ∫ x, (r x - ∫ y, r y ∂π) ^ 2 ∂π := by
  classical
  set c : ℝ := ∫ x, r x ∂π with hc
  set g : X → ℝ := fun x => r x - c with hg
  have hgm : Measurable g := hr.sub measurable_const
  have hrint : Integrable r π := ProbabilityTheory.integrable_of_integrable_sq π r hr hL2
  have hgsq : Integrable (fun x => (g x) ^ 2) π := by
    have hexp : ∀ x, (g x) ^ 2 = (r x) ^ 2 - 2 * c * r x + c ^ 2 := by
      intro x; rw [hg]; ring
    have : Integrable (fun x => (r x) ^ 2 - 2 * c * r x + c ^ 2) π :=
      (hL2.sub (hrint.const_mul (2 * c))).add (integrable_const _)
    exact this.congr (by filter_upwards with x; rw [hexp x])
  have hgmean : ∫ x, g x ∂π = 0 := by
    rw [hg, integral_sub hrint (integrable_const _), integral_const]
    simp [← hc]
  have hRHS : (0 : ℝ) ≤ 4 * N * ∫ x, (g x) ^ 2 ∂π := by
    have : (0 : ℝ) ≤ ∫ x, (g x) ^ 2 ∂π := integral_nonneg (fun x => sq_nonneg _)
    positivity
  -- the sum bound
  have hsum := MarkovChainCLT.integral_sq_sum_coord_le_of_sq_integrable P π hinv N hN (1 / 16)
    (by norm_num) (by norm_num) hrate g hgm hgsq hgmean n
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul]
    simpa using hRHS
  · -- rewrite the integrand
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hkey : ∀ ω : ℕ → X, (Real.sqrt n * (sampleAvg r n ω - c)) ^ 2
        = (n : ℝ)⁻¹ * (∑ k ∈ Finset.range n, g (ω (k + 1))) ^ 2 := by
      intro ω
      have hsplit : ∑ k ∈ Finset.range n, g (ω (k + 1))
          = (∑ k ∈ Finset.range n, r (ω (k + 1))) - (n : ℝ) * c := by
        rw [hg]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
        simp [mul_comm]
      have havg : sampleAvg r n ω - c
          = (n : ℝ)⁻¹ * ((∑ k ∈ Finset.range n, r (ω (k + 1))) - (n : ℝ) * c) := by
        rw [MarkovChainCLT.sampleAvg]
        field_simp
      rw [havg, hsplit, mul_pow, mul_pow, Real.sq_sqrt hnR.le]
      field_simp
    simp only [hkey]
    rw [integral_const_mul]
    have hgoal : ∫ x, (r x - c) ^ 2 ∂π = ∫ x, (g x) ^ 2 ∂π := rfl
    rw [hgoal]
    have hfin : (n : ℝ)⁻¹ * (4 * N * n * ∫ x, (g x) ^ 2 ∂π) = 4 * N * ∫ x, (g x) ^ 2 ∂π := by
      field_simp
    have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
    rw [hfin] at this
    exact this
