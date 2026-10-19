-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.weighted_occupancy_from_total_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T03:14:16.185797+00:00
-- url     : https://prove2.me/submissions/5cbbe56e-4277-4290-946c-de94d40ad0f1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open scoped BigOperators

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta)
    (hweight : ∀ a, 0 ≤ weight a)
    (hsum :
      (∑ i : ι, weight (group i)) <
        (Fintype.card ι : ℝ) * H * (A * (1 - eta))) :
    eta * (Fintype.card ι : ℝ) ≤
      ∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ) := by
  classical
  let good : Finset ι := Finset.univ.filter (fun i => weight (group i) ≤ A * H)
  let bad : Finset ι := Finset.univ.filter (fun i => ¬ weight (group i) ≤ A * H)
  have hcountNat :
      (∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        ((Finset.univ : Finset ι).filter (fun i => group i = a)).card) = good.card := by
    simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset ι)
        ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)) group)
  have hcount :
      (∑ a ∈ ((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)),
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ)) =
        (good.card : ℝ) := by
    simpa only [Nat.cast_sum] using congrArg (fun n : ℕ => (n : ℝ)) hcountNat
  rw [hcount]
  have hcardNat : good.card + bad.card = Fintype.card ι := by
    simpa only [good, bad, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
        (fun i => weight (group i) ≤ A * H))
  have hcard : (good.card : ℝ) + (bad.card : ℝ) = (Fintype.card ι : ℝ) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ)) hcardNat
  have hbad : (bad.card : ℝ) * (A * H) ≤ ∑ i : ι, weight (group i) := by
    calc
      (bad.card : ℝ) * (A * H) = ∑ i ∈ bad, A * H := by simp
      _ ≤ ∑ i ∈ bad, weight (group i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ ≤ ∑ i : ι, weight (group i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro i _ _
          exact hweight (group i)
  have hsum' : (∑ i : ι, weight (group i)) <
      (Fintype.card ι : ℝ) * (A * H) * (1 - eta) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsum
  by_contra h
  have hg : (good.card : ℝ) ≤ eta * (Fintype.card ι : ℝ) :=
    le_of_lt (lt_of_not_ge h)
  have hm := mul_le_mul_of_nonneg_right hg (mul_nonneg hA hH.le)
  have hcard_mul := congrArg (fun x : ℝ => x * (A * H)) hcard
  nlinarith only [hsum', hbad, hm, hcard_mul]
