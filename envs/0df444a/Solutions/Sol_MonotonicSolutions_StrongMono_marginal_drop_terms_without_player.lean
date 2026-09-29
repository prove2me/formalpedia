-- Prove2me | solution 1 for MonotonicSolutions.StrongMono.marginal_drop_terms_without_player
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:19:30.437925+00:00
-- url     : https://prove2.me/submissions/1134816c-d9b8-4ab6-b20b-40004a36ee9b

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

theorem aux_mdt_unan_erase {n : ℕ} (R S : Finset (Fin n)) (i : Fin n) (h : i ∉ R) :
    unanimity R (S.erase i) = unanimity R S := by
  unfold unanimity
  have : R ⊆ S.erase i ↔ R ⊆ S := by
    constructor
    · intro hs x hx; exact Finset.mem_of_mem_erase (hs hx)
    · intro hs x hx
      exact Finset.mem_erase.mpr ⟨fun hxi => h (hxi ▸ hx), hs hx⟩
  simp only [this]

theorem aux_mdt_unan_insert {n : ℕ} (R S : Finset (Fin n)) (i : Fin n) (h : i ∉ R) :
    unanimity R (insert i S) = unanimity R S := by
  unfold unanimity
  have : R ⊆ insert i S ↔ R ⊆ S := by
    constructor
    · intro hs x hx
      rcases Finset.mem_insert.mp (hs hx) with hxi | hxS
      · exact absurd (hxi ▸ hx) h
      · exact hxS
    · intro hs x hx; exact Finset.mem_insert_of_mem (hs hx)
  simp only [this]

theorem aux_mdt_key {n : ℕ} (c : Finset (Fin n) → ℝ) (i : Fin n) (A B : Finset (Fin n))
    (hAB : ∀ R : Finset (Fin n), i ∉ R → unanimity R A = unanimity R B) :
    (∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty ∧ i ∈ R), c R * unanimity R A) -
      (∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty ∧ i ∈ R), c R * unanimity R B) =
    (∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty), c R * unanimity R A) -
      (∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty), c R * unanimity R B) := by
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro R _
  by_cases hi : i ∈ R
  · simp [hi]
  · rw [hAB R hi]
    simp [hi]

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} (c : Finset (Fin n) → ℝ) (i : Fin n)
    (S : Finset (Fin n)) :
    marginal (fun T => ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty ∧ i ∈ R),
        c R * unanimity R T) i S =
      marginal (fun T => ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R T) i S := by
  unfold marginal
  split_ifs with hiS
  · exact aux_mdt_key c i S (S.erase i)
      (fun R hR => (aux_mdt_unan_erase R S i hR).symm)
  · exact aux_mdt_key c i (insert i S) S
      (fun R hR => aux_mdt_unan_insert R S i hR)
