-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.delay_sum_bounded
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:10:45.595975+00:00
-- url     : https://prove2.me/submissions/34926884-8316-477c-9970-bfcfd48b0283

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

open MeasureTheory ProbabilityTheory

open LargeDelaySGD.MeanSquare in
theorem solution (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (hreg : BoundedRegime α s) :
    Summable (fun n => α (n + 1) ^ 2) ∧ Summable (delaySum α s) := by
  obtain ⟨⟨D, hD⟩, hsq, -⟩ := hreg
  have hsh : ∀ j, Summable (fun n => α (n + j) ^ 2) := fun j =>
    (summable_nat_add_iff (f := fun n => α n ^ 2) j).2 hsq
  have hsh1 : ∀ j, Summable (fun n => α (n + j + 1) ^ 2) := fun j => hsh (j + 1)
  refine ⟨hsh 1, ?_⟩
  have hnn : ∀ n, 0 ≤ delaySum α s n := fun n =>
    mul_nonneg (hα _).le (Finset.sum_nonneg fun r _ => (hα _).le)
  rw [← summable_nat_add_iff D]
  refine Summable.of_nonneg_of_le (fun n => hnn (n + D)) (fun n => ?_)
    (summable_sum (s := Finset.range D) fun k _ => ((hsh1 D).add (hsh1 k)).div_const 2)
  show delaySum α s (n + D) ≤ ∑ k ∈ Finset.range D, (α (n + D + 1) ^ 2 + α (n + k + 1) ^ 2) / 2
  unfold delaySum
  have hsub : Finset.Ico (s (n + D)) (n + D) ⊆ Finset.Ico n (n + D) :=
    Finset.Ico_subset_Ico (by have := hD (n + D); omega) le_rfl
  calc α (n + D + 1) * ∑ r ∈ Finset.Ico (s (n + D)) (n + D), α (r + 1)
      ≤ α (n + D + 1) * ∑ r ∈ Finset.Ico n (n + D), α (r + 1) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => (hα _).le)) (hα _).le
    _ = ∑ k ∈ Finset.range D, α (n + D + 1) * α (n + k + 1) := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range D, (α (n + D + 1) ^ 2 + α (n + k + 1) ^ 2) / 2 :=
        Finset.sum_le_sum fun k _ => by nlinarith [sq_nonneg (α (n + D + 1) - α (n + k + 1))]
