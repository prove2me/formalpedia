-- Prove2me | solution 1 for MeasureTheory.mul_upcrossingsBefore_le_sum_add_posPart
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T05:47:09.098352+00:00
-- url     : https://prove2.me/submissions/30ea8d2d-d72a-4b1e-af81-9d48a4624793

import Mathlib.Probability.Martingale.Upcrossing

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/


namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}



theorem _root_.solution (hab : a < b) :
    (b - a) * upcrossingsBefore a b f N ω ≤
      (∑ k ∈ Finset.range N, upcrossingStrat a b f N k ω * (f (k + 1) - f k) ω) + (a - f N ω)⁺ := by
  by_cases hN : N = 0
  · simp [hN, posPart_nonneg]
  simp_rw [upcrossingStrat, Finset.sum_mul, ←
    Set.indicator_mul_left _ _ (fun x ↦ (f (x + 1) - f x) ω), Pi.one_apply, Pi.sub_apply, one_mul]
  rw [Finset.sum_comm]
  have h₁ : ∀ k, ∑ n ∈ Finset.range N, (Set.Ico (lowerCrossingTime a b f N k ω)
      (upperCrossingTime a b f N (k + 1) ω)).indicator (fun m => f (m + 1) ω - f m ω) n =
      stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (k + 1) ω : ℕ)) ω -
        stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N k ω : ℕ)) ω := by
    intro k
    rw [Finset.sum_indicator_eq_sum_filter, (_ : Finset.filter (fun i => i ∈ Set.Ico
      (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)) (Finset.range N) =
      Finset.Ico (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)),
      Finset.sum_Ico_eq_add_neg _ lowerCrossingTime_le_upperCrossingTime_succ,
      Finset.sum_range_sub fun n => f n ω, Finset.sum_range_sub fun n => f n ω, neg_sub,
      sub_add_sub_cancel]
    · rfl
    · ext i
      simp only [Set.mem_Ico, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
        and_iff_right_iff_imp, and_imp]
      exact fun _ h => lt_of_lt_of_le h upperCrossingTime_le
  simp_rw [h₁]
  set g : ℕ → ℝ := fun k => stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (k + 1) ω : ℕ)) ω -
        stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N k ω : ℕ)) ω with hg
  set U := upcrossingsBefore a b f N ω with hU
  have hUle : U ≤ N := upcrossingsBefore_le f ω hab
  have hA : ∑ _k ∈ Finset.range U, (b - a) ≤ ∑ k ∈ Finset.range U, g k := by
    gcongr ∑ k ∈ _, ?_ with i hi
    refine le_sub_of_le_upcrossingsBefore (zero_lt_iff.2 hN) hab ?_
    rwa [Finset.mem_range] at hi
  have hB : -(a - f N ω)⁺ ≤ ∑ k ∈ Finset.Ico U N, g k := by
    by_cases hUN : U < N
    · rw [Finset.sum_eq_sum_Ico_succ_bot hUN]
      have hz : ∑ k ∈ Finset.Ico (U + 1) N, g k = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_Ico] at hi
        exact sub_eq_zero_of_upcrossingsBefore_lt hab (by omega)
      rw [hz, add_zero, hg]
      simp only
      have hup : stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (U + 1) ω : ℕ)) ω = f N ω := by
        simp only [stoppedValue]
        rw [upperCrossingTime_eq_of_upcrossingsBefore_lt hab (Nat.lt_succ_self _)]
        rfl
      rw [hup]
      by_cases heq : lowerCrossingTime a b f N U ω = N
      · have : stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N U ω : ℕ)) ω = f N ω := by
          simp only [stoppedValue]; rw [heq]
          rfl
        rw [this, sub_self]; exact neg_nonpos.2 (posPart_nonneg _)
      · have h3 := stoppedValue_lowerCrossingTime (f := f) (ω := ω) heq
        have h4 := le_posPart (a - f N ω)
        linarith
    · have : U = N := le_antisymm hUle (not_lt.1 hUN)
      rw [this, Finset.Ico_self, Finset.sum_empty]; exact neg_nonpos.2 (posPart_nonneg _)
  have hsplit := Finset.sum_range_add_sum_Ico g hUle
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hA
  rw [← hsplit]
  nlinarith
