-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:19:27.779478+00:00
-- url     : https://prove2.me/submissions/7d254514-c80d-4e4c-bb81-5d694f4555e1

import Mathlib.Probability.Martingale.Basic

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
include h𝒢mono hYmeas in
/-- A partial sum of martingale differences is measurable for the σ-algebra at its top index. -/
theorem LevyStochCalc.Probability.stronglyMeasurable_sum_range (n : ℕ) :
    StronglyMeasurable[𝒢 n] (fun ω => ∑ i ∈ Finset.range n, Y i ω) := by
  refine @Finset.stronglyMeasurable_fun_sum Ω ℝ _ _ _ (𝒢 n) _ _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  exact (hYmeas i).mono (h𝒢mono hi)
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc.Probability in
include h𝒢le h𝒢mono hY hYmeas hYcond in
/-- A partial sum of martingale differences is orthogonal to the next difference. -/
theorem solution (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂P = 0 := by
  haveI : SigmaFinite (P.trim (h𝒢le n)) := by
    haveI : IsFiniteMeasure (P.trim (h𝒢le n)) :=
      ⟨by rw [MeasureTheory.trim_measurableSet_eq (h𝒢le n) MeasurableSet.univ]
          exact measure_lt_top P Set.univ⟩
    infer_instance
  have hSmem := LevyStochCalc.Probability.memLp_sum_range Y hY n
  have hSmeas := LevyStochCalc.Probability.stronglyMeasurable_sum_range 𝒢 h𝒢mono Y hYmeas n
  have hprod : Integrable
      ((fun ω => ∑ i ∈ Finset.range n, Y i ω) * Y n) P := hSmem.integrable_mul (hY n)
  have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := 𝒢 n) hSmeas hprod
    ((hY n).integrable (by norm_num))
  have hzero : P[(fun ω => ∑ i ∈ Finset.range n, Y i ω) * Y n | 𝒢 n] =ᵐ[P] 0 := by
    filter_upwards [hkey, hYcond n] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', Pi.zero_apply, mul_zero]
  calc ∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂P
      = ∫ ω, ((fun ω => ∑ i ∈ Finset.range n, Y i ω) * Y n) ω ∂P := rfl
    _ = ∫ ω, (P[(fun ω => ∑ i ∈ Finset.range n, Y i ω) * Y n | 𝒢 n]) ω ∂P :=
        (MeasureTheory.integral_condExp (h𝒢le n)).symm
    _ = 0 := by rw [integral_congr_ae hzero]; simp
