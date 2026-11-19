-- Prove2me | solution 1 for ManipPotential.theorem_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:22:31.562478+00:00
-- url     : https://prove2.me/submissions/6c624222-09f6-4bd0-9d0a-d199cee185a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ManipPotential_Anonymous
import Definitions.Def_ManipPotential_Onto
import Definitions.Def_ManipPotential_manipPotentialAt
import Theorems.Thm_ManipPotential_lemma_6_2
import Theorems.Thm_ManipPotential_lambda_one_impossible
import Theorems.Thm_ManipPotential_proposition_6_12
import Theorems.Thm_ManipPotential_cycle_dependency_bound

open ManipPotential

theorem solution {m : ℕ} (f : List (Ranking m) → Fin m) (hA : Anonymous f) (hO : Onto f)
    (K : ℕ) (hK : ∀ n : ℕ, manipPotentialAt f n ≤ K) : m ≤ K + 2 := by
  by_cases hm : 3 ≤ m
  swap
  · omega
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨g, hg⟩ := lemma_6_2 hm f hA hO K hK
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    exact absurd ⟨g, hg⟩ (lambda_one_impossible hm)
  obtain ⟨W, hW, hw⟩ := proposition_6_12 hm K g hg
  have hne : ∀ i : Fin m, i ≠ i + 1 := by
    intro i h
    have h1 : (1 : Fin m) = 0 := by
      have := congrArg (fun x => x - i) h
      simpa using this.symm
    have : ((1 : Fin m) : ℕ) = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [h1] at this
    simp at this
  choose w hwW hwC hwn using fun i : Fin m => hw i (i + 1) (hne i)
  have hlam : (1 : ℝ) < (K : ℝ) + 1 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
    linarith
  have := cycle_dependency_bound hm ((K : ℝ) + 1) hlam W hW w hwW hwC hwn
  have h' : ((m : ℕ) : ℝ) ≤ ((K + 2 : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast h'
