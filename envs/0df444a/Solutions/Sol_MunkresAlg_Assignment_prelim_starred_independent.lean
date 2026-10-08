-- Prove2me | solution 1 for MunkresAlg.Assignment.prelim_starred_independent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:14:17.627974+00:00
-- url     : https://prove2.me/submissions/db010ba6-f5f8-46de-9d94-fffdee9668b5

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm



namespace MunkresAlg.Assignment

open Classical

theorem greedyStar_inv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (L : List (Fin n × Fin n)) :
    ∀ S : Finset (Fin n × Fin n), IsIndepZeros B S →
      IsIndepZeros B (L.foldl (fun S z => if B z.1 z.2 = 0 ∧ ∀ q ∈ S, q.1 ≠ z.1 ∧ q.2 ≠ z.2 then insert z S else S) S) := by
  induction L with
  | nil => intro S h; exact h
  | cons z L ih =>
    intro S hS
    simp only [List.foldl_cons]
    apply ih
    split_ifs with hc
    · obtain ⟨hI, hz⟩ := hS
      refine ⟨?_, ?_⟩
      · intro p hp q hq hpq
        rw [Finset.mem_insert] at hp hq
        rcases hp with rfl | hp <;> rcases hq with rfl | hq
        · exact absurd rfl hpq
        · have := hc.2 q hq
          exact ⟨fun h => this.1 h.symm, fun h => this.2 h.symm⟩
        · exact hc.2 p hp
        · exact hI p hp q hq hpq
      · intro p hp
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hc.1
        · exact hz p hp
    · exact hS

theorem ps_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : IsStart A s) :
    IsIndepZeros s.A s.starred := by
  obtain ⟨L, -, -, rfl⟩ := hs
  have h := greedyStar_inv (prelimMatrix A) L ∅ ⟨by intro p hp; simp at hp, by intro p hp; simp at hp⟩
  unfold enterStep1
  split_ifs <;> exact h

end MunkresAlg.Assignment

open MunkresAlg.Assignment


theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (hs : IsStart A s) :
    IsIndepZeros s.A s.starred := by
  exact ps_core A s hs
