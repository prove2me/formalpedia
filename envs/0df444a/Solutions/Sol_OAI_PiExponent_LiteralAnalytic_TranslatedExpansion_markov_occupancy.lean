-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.markov_occupancy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:44:25.873979+00:00
-- url     : https://prove2.me/submissions/8e38ff0e-a968-49a0-b25b-0d9f3c1e257b

import Mathlib
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) {t eta : ℝ}
    (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (hf : ∀ i, 0 ≤ f i)
    (hsum : (∑ i : ι, f i) < (Fintype.card ι : ℝ) * t * (1 - eta)) :
    eta * (Fintype.card ι : ℝ) ≤
      ((Finset.univ : Finset ι).filter (fun i => f i ≤ t)).card := by
  by_contra hcon
  push Not at hcon
  set S := (Finset.univ : Finset ι).filter (fun i => f i ≤ t)
  set T := (Finset.univ : Finset ι).filter (fun i => ¬ f i ≤ t)
  have hcard : (S.card : ℝ) + T.card = Fintype.card ι := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι)) (fun i => f i ≤ t)
    rw [Finset.card_univ] at this
    exact_mod_cast this
  have hT : t * T.card ≤ ∑ i ∈ T, f i := by
    have : ∑ i ∈ T, t ≤ ∑ i ∈ T, f i := Finset.sum_le_sum (fun i hi => by
      simp only [T, Finset.mem_filter] at hi; linarith [hi.2])
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  have hsub : ∑ i ∈ T, f i ≤ ∑ i : ι, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hf i)
  have : (Fintype.card ι : ℝ) * (1 - eta) ≤ T.card := by linarith
  nlinarith
