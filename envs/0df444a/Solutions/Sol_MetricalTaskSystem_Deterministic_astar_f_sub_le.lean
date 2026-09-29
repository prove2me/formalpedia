-- Prove2me | solution 1 for MetricalTaskSystem.Deterministic.astar_f_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:31:35.232202+00:00
-- url     : https://prove2.me/submissions/a954ab12-787b-4f18-a2aa-c4e843e0e858

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD

namespace MetricalTaskSystem.Deterministic

theorem aux_afsl_nonneg {S : Type} (d : S → S → ℝ) (hd : IsTaskSystem d) (a b : S) :
    0 ≤ d a b := by
  by_cases h : a = b
  · subst h; rw [hd.diag]
  · exact le_of_lt (hd.pos a b h)

theorem aux_afsl_main {S : Type} [DecidableEq S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (k : ℕ) : ∀ x y : S, fSeq d s k x - fSeq d s k y ≤ d y x := by
  induction k with
  | zero =>
    intro x y
    simp only [fSeq, sub_self]
    exact aux_afsl_nonneg d hd y x
  | succ k ih =>
    intro x y
    obtain ⟨hne, hmin⟩ := hs.2 k
    have ex : ∀ z, fSeq d s (k + 1) z =
        if z = s k then fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k) else fSeq d s k z :=
      fun z => rfl
    rw [ex x, ex y]
    by_cases hx : x = s k <;> by_cases hy : y = s k
    · rw [if_pos hx, if_pos hy, sub_self, hx, hy, hd.diag]
    · rw [if_pos hx, if_neg hy, hx]
      have := hmin y hy
      linarith
    · rw [if_neg hx, if_pos hy, hy]
      have h1 := ih x (s (k + 1))
      have h2 := hd.triangle (s (k + 1)) (s k) x
      linarith
    · rw [if_neg hx, if_neg hy]
      exact ih x y

end MetricalTaskSystem.Deterministic

open MetricalTaskSystem.Deterministic

theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (k : ℕ) (x y : S) :
    fSeq d s k x - fSeq d s k y ≤ d y x :=
  aux_afsl_main d hd s₀ s hs k x y
