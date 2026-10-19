-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.coeff_pow_eq_bounded_fin_tuple_sum_generic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:23:09.557905+00:00
-- url     : https://prove2.me/submissions/12d76501-edbf-4860-b36a-ea43ae42926b

import Mathlib
import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation


theorem solution (q k : ℕ) (f : ℕ → ℂ) :
    PowerSeries.coeff k ((PowerSeries.mk f) ^ q) =
      ∑ a ∈ (Finset.univ : Finset (Fin q → Fin (k + 1))).filter
        (fun a => (∑ i : Fin q, (a i : ℕ)) = k), ∏ i : Fin q, f (a i) := by
  classical
  have hpow : (PowerSeries.mk f) ^ q = ∏ _j : Fin q, PowerSeries.mk f := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hpow, PowerSeries.coeff_prod]
  simp only [PowerSeries.coeff_mk]
  have hle : ∀ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin q)) k, ∀ i, l i < k + 1 := by
    intro l hl i
    rw [Finset.mem_finsuppAntidiag] at hl
    obtain ⟨hs, -⟩ := hl
    rw [← hs]
    exact Nat.lt_succ_of_le (Finset.single_le_sum (f := fun j => l j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
  refine Finset.sum_nbij' (fun l => fun i => if h : l ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin q)) k
      then ⟨l i, hle l h i⟩ else 0)
    (fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, dif_pos hl]
    exact (Finset.mem_finsuppAntidiag.mp hl).1
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    simpa using ha
  · intro l hl
    have hs := (Finset.mem_finsuppAntidiag.mp hl).1
    ext i
    simp [hs]
  · intro a ha
    have hm : Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ)) ∈
        Finset.finsuppAntidiag (Finset.univ : Finset (Fin q)) k := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [Finset.mem_finsuppAntidiag]
      refine ⟨?_, by simp⟩
      simpa using ha
    have hs : ∑ i, ((a i : ℕ)) = k := by simpa using ha
    funext i
    simp [hs]
  · intro l hl
    have hs := (Finset.mem_finsuppAntidiag.mp hl).1
    simp [hs]

