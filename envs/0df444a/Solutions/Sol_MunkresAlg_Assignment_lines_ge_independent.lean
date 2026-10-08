-- Prove2me | solution 1 for MunkresAlg.Assignment.lines_ge_independent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:14:14.863753+00:00
-- url     : https://prove2.me/submissions/b8d4fa44-ada4-49cd-8830-05bdf9178bf9

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic



namespace MunkresAlg.Assignment

open Classical

theorem lg_core {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n))
    (hcov : CoversZeros B R C) :
    maxIndepZeros B ≤ R.card + C.card := by
  unfold maxIndepZeros
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_filter] at hS
  obtain ⟨hI, hz⟩ := hS.2
  have h1 : (S.filter (fun p => p.1 ∈ R)).card ≤ R.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      exact hp.2
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      by_contra hne
      exact (hI p hp.1 q hq.1 hne).1 hpq
  have h2 : (S.filter (fun p => ¬ p.1 ∈ R)).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
      rcases hcov p.1 p.2 (hz p hp.1) with h | h
      · exact absurd h hp.2
      · exact h
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      by_contra hne
      exact (hI p hp.1 q hq.1 hne).2 hpq
  have := Finset.card_filter_add_card_filter_not (s := S) (fun p => p.1 ∈ R)
  omega

end MunkresAlg.Assignment

open MunkresAlg.Assignment


theorem solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (R C : Finset (Fin n))
    (hcov : CoversZeros B R C) :
    maxIndepZeros B ≤ R.card + C.card := by
  exact lg_core B R C hcov
