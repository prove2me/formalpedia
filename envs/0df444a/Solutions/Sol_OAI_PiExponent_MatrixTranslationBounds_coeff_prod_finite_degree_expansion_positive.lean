-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_finite_degree_expansion_positive
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:48:40.222044+00:00
-- url     : https://prove2.me/submissions/199f2c31-0ad6-4167-ab7b-17afebd66e28

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → PowerSeries ℂ) (k : ℕ)
    (h0 : ∀ i, PowerSeries.coeff 0 (g i) = 0) :
    (∑ f : ι → Fin (k + 1),
      if (∑ i, (f i).val) = k then
        ∏ i, PowerSeries.coeff (f i).val (g i)
      else 0) =
    ∑ f : ι → Fin (k + 1),
      if (∀ i, 0 < (f i).val) ∧ (∑ i, (f i).val) = k then
        ∏ i, PowerSeries.coeff (f i).val (g i)
      else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro f _
  by_cases hs : (∑ i, (f i).val) = k
  · by_cases hp : ∀ i, 0 < (f i).val
    · simp [hs, hp]
    · push_neg at hp
      obtain ⟨i, hi⟩ := hp
      have hzero : (f i).val = 0 := by omega
      have hprod : (∏ i, PowerSeries.coeff (f i).val (g i)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [hzero]
        exact h0 i
      simp [hs, hprod]
  · simp [hs]