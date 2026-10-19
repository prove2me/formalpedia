-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.masked_sum_le_valid_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:47:59.595993+00:00
-- url     : https://prove2.me/submissions/7f102554-c363-48f2-b8a7-183addbca421

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-!
The mask discards invalid coefficient assignments. Each retained product has
norm at most one; the sum is therefore bounded by the mask's cardinality.
-/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    [DecidablePred (fun f : ι → Fin (k + 1) =>
      (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k)]
    (h1 : ∀ i n, ‖PowerSeries.coeff n (g i)‖ ≤ (1 : ℝ)) :
    (∑ f : ι → Fin (k + 1),
      ‖if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
          ∏ i, PowerSeries.coeff (f i).val (g i)
        else (0 : ℂ)‖) ≤
      (Fintype.card {f : ι → Fin (k + 1) //
        (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k} : ℝ) := by
  classical
  let Valid (f : ι → Fin (k + 1)) : Prop :=
    (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k
  let S : Finset (ι → Fin (k + 1)) := Finset.univ.filter Valid
  have hprod (f : ι → Fin (k + 1)) :
      ‖∏ i, PowerSeries.coeff (f i).val (g i)‖ ≤ (1 : ℝ) := by
    rw [norm_prod]
    calc
      (∏ i, ‖PowerSeries.coeff (f i).val (g i)‖) ≤
          ∏ _i : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _
          exact norm_nonneg _
        · intro i _
          exact h1 i _
      _ = 1 := by simp
  have hsum :
      (∑ f : ι → Fin (k + 1),
        ‖if Valid f then ∏ i, PowerSeries.coeff (f i).val (g i)
          else (0 : ℂ)‖) ≤
      ∑ f : ι → Fin (k + 1), if Valid f then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro f _
    by_cases hf : Valid f
    · simpa [hf] using hprod f
    · simp [hf]
  have hcard : S.card =
      Fintype.card {f : ι → Fin (k + 1) // Valid f} := by
    exact (Fintype.card_subtype Valid).symm
  calc
    (∑ f : ι → Fin (k + 1),
      ‖if Valid f then ∏ i, PowerSeries.coeff (f i).val (g i)
        else (0 : ℂ)‖) ≤
        ∑ f : ι → Fin (k + 1), if Valid f then (1 : ℝ) else 0 := hsum
    _ = (S.card : ℝ) := by
      simp only [S, Finset.card_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ = (Fintype.card {f : ι → Fin (k + 1) // Valid f} : ℝ) := by
      exact_mod_cast hcard
