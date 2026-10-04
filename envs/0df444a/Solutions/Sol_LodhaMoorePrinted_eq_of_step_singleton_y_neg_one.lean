-- Prove2me | solution 1 for LodhaMoorePrinted.eq_of_step_singleton_y_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T19:34:53.910996+00:00
-- url     : https://prove2.me/submissions/1ead83b9-1dd7-432d-acc8-7b5acf1184af

import Definitions.Def_LodhaMooreWords
import Mathlib

section
namespace LodhaMoorePrinted

open LodhaMoore

/-- The only substitution that applies to the one-letter word `y_s⁻¹` is the expansion
`y_s⁻¹ ⇒ x_s⁻¹ y_{s00}⁻¹ y_{s01} y_{s1}⁻¹`, which is not on the p. 9 list. -/
theorem eq_of_step_singleton_y_neg_one (s : LodhaMoore.Seq) (W : LodhaMoore.Word)
    (h : LodhaMoore.Step [(.y s, -1)] W) :
    W = [(.x s, -1), (.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1),
      (.y (s ++ [true]), -1)] := by
  generalize hW0 : [(Gen.y s, -1)] = W0 at h
  have two : ∀ (pre post : Word) (a b : Gen × ℤ), [(Gen.y s, -1)] ≠ pre ++ [a, b] ++ post := by
    intro pre post a b h
    have := congrArg List.length h
    simp at this <;> omega
  have one : ∀ (pre post : Word) (a : Gen × ℤ), [(Gen.y s, -1)] = pre ++ [a] ++ post →
      pre = [] ∧ post = [] ∧ a = (Gen.y s, -1) := by
    intro pre post a h
    rcases pre with _ | ⟨p, pre⟩
    · rcases post with _ | ⟨q, post⟩
      · simp at h ⊢; try exact h.symm
      · simp at h
    · have := congrArg List.length h
      simp at this <;> omega
  cases h with
  | moveX pre post s' t t' i _ => exact absurd hW0 (two _ _ _ _)
  | moveXInv pre post s' t t' i _ => exact absurd hW0 (two _ _ _ _)
  | commute pre post u v i j _ => exact absurd hW0 (two _ _ _ _)
  | merge pre post g i j _ _ _ => exact absurd hW0 (two _ _ _ _)
  | cancel pre post s' i _ => exact absurd hW0 (two _ _ _ _)
  | expand pre post s' =>
    obtain ⟨-, -, h⟩ := one _ _ _ hW0
    simp at h
  | expandInv pre post s' =>
    obtain ⟨rfl, rfl, h⟩ := one _ _ _ hW0
    simp only [Prod.mk.injEq, Gen.y.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | split pre post g i j hi hj hij =>
    obtain ⟨-, -, h⟩ := one _ _ _ hW0
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, h⟩ := h
    rcases lt_or_gt_of_ne hi with hi' | hi'
    · have : j < 0 := by nlinarith
      omega
    · have : 0 < j := by nlinarith
      omega


end LodhaMoorePrinted
end


open LodhaMoorePrinted in
theorem solution (s : LodhaMoore.Seq) (Ω : LodhaMoore.Word)
    (h : LodhaMoore.Step [(.y s, -1)] Ω) :
    Ω = [(.x s, -1), (.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1),
      (.y (s ++ [true]), -1)] :=
  by
  try haveI := s; try haveI := Ω; try haveI := h; first
    | exact LodhaMoorePrinted.eq_of_step_singleton_y_neg_one s Ω h
    | exact LodhaMoorePrinted.eq_of_step_singleton_y_neg_one
    | exact LodhaMoorePrinted.eq_of_step_singleton_y_neg_one ..
    | (apply LodhaMoorePrinted.eq_of_step_singleton_y_neg_one <;> first | assumption | infer_instance)
    | simpa using LodhaMoorePrinted.eq_of_step_singleton_y_neg_one
