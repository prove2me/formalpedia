-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:20:49.60461+00:00
-- url     : https://prove2.me/submissions/d8d89ab8-03dd-4bbe-a448-22bb1baf0f00

import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_LevyStochCalc_Probability_integral_sum_mul_of_condExp_eq_zero_408915f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/MartingaleDifference.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
open MeasureTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
section MartingaleDifference
variable (𝒢 : ℕ → MeasurableSpace Ω) (h𝒢le : ∀ k, 𝒢 k ≤ mΩ) (h𝒢mono : Monotone 𝒢)
  (Y : ℕ → Ω → ℝ) (hY : ∀ k, MemLp (Y k) 2 P)
  (hYmeas : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (Y k))
  (hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0)
include hY in
omit [IsProbabilityMeasure P] in
/-- A partial sum of martingale differences lies in `L²`. -/
theorem LevyStochCalc.Probability.memLp_sum_range (n : ℕ) : MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 P :=
  memLp_finsetSum _ fun i _ => hY i
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc.Probability in
include h𝒢le h𝒢mono hY hYmeas hYcond in
/-- **Orthogonality of martingale differences.** The second moment of a sum of martingale
differences is the sum of the second moments. -/
theorem solution (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
      = ∑ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hSmem := LevyStochCalc.Probability.memLp_sum_range Y hY n
    have hSint : Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2) P := by
      have hfun : (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2)
          = (fun ω => ∑ i ∈ Finset.range n, Y i ω)
            * (fun ω => ∑ i ∈ Finset.range n, Y i ω) := by
        funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact hSmem.integrable_mul hSmem
    have hYint : Integrable (fun ω => (Y n ω) ^ 2) P := by
      have hfun : (fun ω => (Y n ω) ^ 2) = Y n * Y n := by
        funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hY n).integrable_mul (hY n)
    have hcross : Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) P :=
      hSmem.integrable_mul (hY n)
    have hexp : ∀ ω, (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2
        = (∑ i ∈ Finset.range n, Y i ω) ^ 2
          + 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω) + (Y n ω) ^ 2 := by
      intro ω
      rw [Finset.sum_range_succ]
      ring
    have hsum2 : Integrable
        (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
          + 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω)) P :=
      hSint.add (hcross.const_mul 2)
    simp_rw [hexp]
    rw [integral_add hsum2 hYint, integral_add hSint (hcross.const_mul 2),
      integral_const_mul, LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero_408915f 𝒢 h𝒢le h𝒢mono Y hY hYmeas hYcond n,
      Finset.sum_range_succ, ih]
    ring
