-- Prove2me | solution 1 for OAI.PiExponent.extend_positive_separated_weights
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:59:28.974946+00:00
-- url     : https://prove2.me/submissions/dba083a6-cb99-4c71-988e-9ce2603c824e

import Mathlib
import Definitions.Def_PiExponent_DeterminantSetup

theorem solution
    (S : List ℕ → ℕ) (m : ℕ) (w : Fin m → ℕ)
    (hw : ∀ i, 0 < w i)
    (hsep : OAI.PiExponent.separatedWeights S w) :
    ∃ w' : Fin (m + 1) → ℕ,
      (∀ i, 0 < w' i) ∧ OAI.PiExponent.separatedWeights S w' := by
  set N := max 1 (S (List.ofFn w)) with hN
  refine ⟨fun i => if h : i.val < m then w ⟨i.val, h⟩ else N, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with h
    · exact hw _
    · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · rintro ⟨i, hi⟩
    by_cases h : i < m
    · have hl : (List.ofFn (fun k : Fin (⟨i, hi⟩ : Fin (m + 1)).val =>
          (fun j : Fin (m + 1) => if h : j.val < m then w ⟨j.val, h⟩ else N)
            ⟨k.val, Nat.lt_trans k.isLt hi⟩)) =
          List.ofFn (fun k : Fin (⟨i, h⟩ : Fin m).val => w ⟨k.val, Nat.lt_trans k.isLt h⟩) := by
        congr 1
        funext k
        simp only
        rw [dif_pos (Nat.lt_trans k.isLt h)]
      simp only at hl ⊢
      rw [hl, dif_pos h]
      exact hsep ⟨i, h⟩
    · have him : i = m := by omega
      subst him
      simp only [lt_irrefl, dite_false]
      have hl : (List.ofFn (fun k : Fin i =>
          (fun j : Fin (i + 1) => if h : j.val < i then w ⟨j.val, h⟩ else N)
            ⟨k.val, Nat.lt_trans k.isLt hi⟩)) = List.ofFn w := by
        congr 1
        funext k
        simp only
        rw [dif_pos k.isLt]
      rw [hl]
      exact le_max_right _ _
