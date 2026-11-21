-- Prove2me | solution 1 for MasulloGRH.sobolev_admissible_jet_count
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:27:05.389194+00:00
-- url     : https://prove2.me/submissions/89b31055-77e8-40c1-8e3f-f85d0cb76df3

import Theorems.Thm_MasulloGRH_sobolev_jet_weight_integrable_iff
import Mathlib.Order.Interval.Set.Nat
set_option autoImplicit false
open MeasureTheory Set

theorem solution (N : ℕ) (s : ℝ) (hs : 1 < s) :
    {m : ℕ | m < N ∧ Integrable (fun x : ℝ =>
      x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))}.ncard =
      min N (Nat.ceil ((s - 1) / 2)) := by
  have heq : {m : ℕ | m < N ∧ Integrable (fun x : ℝ =>
      x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))} = Iio (min N (Nat.ceil ((s - 1) / 2))) := by
    ext m
    simp only [mem_ofPred_eq, mem_Iio, lt_min_iff, Nat.lt_ceil,
      MasulloGRH.sobolev_jet_weight_integrable_iff m s hs]
    constructor
    · rintro ⟨hm, h⟩
      exact ⟨hm, by linarith⟩
    · rintro ⟨hm, h⟩
      exact ⟨hm, by linarith⟩
  rw [heq, ncard_Iio_nat]

example : {m : ℕ | m < 2 ∧ Integrable (fun x : ℝ =>
    x ^ (2 * m) / (1 + x ^ 2) ^ ((3 : ℝ) / 2))}.ncard = 1 := by
  rw [solution 2 3 (by norm_num)]
  norm_num

example : min 2 (Nat.floor (((3 : ℝ) - 1) / 2) + 1) = 2 := by norm_num
