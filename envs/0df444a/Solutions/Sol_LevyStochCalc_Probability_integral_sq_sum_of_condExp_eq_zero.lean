-- Prove2me | solution 1 for LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:55:37.35458+00:00
-- url     : https://prove2.me/submissions/9765b1dc-ce37-46b7-83eb-91f9f69a51b4

import Definitions.Def_LevyStochCalc_Probability_MartingaleDifference_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of martingale differences

A finite family `Y 0, …, Y (n-1)` in `L²` with `Y k` measurable for `𝒢 (k+1)` and
`𝔼[Y k | 𝒢 k] = 0` is orthogonal, so the second moment of the sum is the sum of the second
moments.

## Main statements

* `LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero` — a partial sum is orthogonal
  to the next difference.
* `LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero` — the second moment of a sum of
  martingale differences is the sum of the second moments.
-/

namespace LevyStochCalc.Probability

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

section MartingaleDifference

variable (𝒢 : ℕ → MeasurableSpace Ω) (h𝒢le : ∀ k, 𝒢 k ≤ mΩ) (h𝒢mono : Monotone 𝒢)
  (Y : ℕ → Ω → ℝ) (hY : ∀ k, MemLp (Y k) 2 P)
  (hYmeas : ∀ k, StronglyMeasurable[𝒢 (k + 1)] (Y k))
  (hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0)


include h𝒢le h𝒢mono hY hYmeas hYcond in

theorem _root_.solution (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
      = ∑ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P := by
  have hSL2 : ∀ n, MemLp (fun ω => ∑ i ∈ Finset.range n, Y i ω) 2 P := fun n =>
    memLp_finsetSum _ fun i _ => hY i
  have hSm : ∀ n, StronglyMeasurable[𝒢 n] (fun ω => ∑ i ∈ Finset.range n, Y i ω) := by
    intro n
    refine Finset.stronglyMeasurable_fun_sum _ fun i hi => ?_
    exact (hYmeas i).mono (h𝒢mono (by simp at hi; omega))
  have horth : ∀ n, ∫ ω, (∑ i ∈ Finset.range n, Y i ω) * Y n ω ∂P = 0 := by
    intro n
    have hint : Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) P :=
      (hSL2 n).integrable_mul (hY n)
    rw [← integral_condExp (h𝒢le n)]
    have h1 : P[(fun ω => (∑ i ∈ Finset.range n, Y i ω) * Y n ω) | 𝒢 n] =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, Y i ω)) * P[Y n | 𝒢 n] :=
      condExp_mul_of_stronglyMeasurable_left (hSm n) hint ((hY n).integrable one_le_two)
    rw [integral_congr_ae h1]
    have h2 : (fun ω => (∑ i ∈ Finset.range n, Y i ω)) * P[Y n | 𝒢 n] =ᵐ[P] 0 := by
      filter_upwards [hYcond n] with ω hω
      simp [hω]
    rw [integral_congr_ae h2]
    simp
  induction n with
  | zero => simp
  | succ n ih =>
    have hexp : (fun ω => (∑ i ∈ Finset.range (n + 1), Y i ω) ^ 2) =
        fun ω => ((∑ i ∈ Finset.range n, Y i ω) ^ 2 + 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω))
          + Y n ω ^ 2 := by
      funext ω; rw [Finset.sum_range_succ]; ring
    have i1 : Integrable (fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2) P := (hSL2 n).integrable_sq
    have i2 : Integrable (fun ω => 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω)) P :=
      ((hSL2 n).integrable_mul (hY n)).const_mul 2
    have i3 : Integrable (fun ω => Y n ω ^ 2) P := (hY n).integrable_sq
    rw [hexp, integral_add (f := fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
        + 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω)) (g := fun ω => Y n ω ^ 2) (i1.add i2) i3,
      integral_add (f := fun ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2)
        (g := fun ω => 2 * ((∑ i ∈ Finset.range n, Y i ω) * Y n ω)) i1 i2,
      integral_const_mul, horth n, ih,
      Finset.sum_range_succ]
    ring
