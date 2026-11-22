-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.gridStopAux_eq
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:45:54.399912+00:00
-- url     : https://prove2.me/submissions/0e696660-aa71-46e7-8f72-025042132d57

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F000

open LevyStochCalc.Brownian.Ito

theorem solution {Ω : Type*} (τ : Ω → WithTop ℝ) (t : ℝ) (n k : ℕ) (ω : Ω) :
    (∃ j ≤ k, gridStopAux τ t n k ω = ((gridPt t n j : ℝ) : WithTop ℝ))
      ∨ gridStopAux τ t n k ω = ⊤ := by
  induction k with
  | zero =>
    rcases stepStop_eq_or τ (gridPt t n 0) ω with h | h
    · exact Or.inl ⟨0, le_rfl, h⟩
    · exact Or.inr h
  | succ k ih =>
    by_cases h : stepStop τ (gridPt t n (k+1)) ω ≤ gridStopAux τ t n k ω
    · simp only [gridStopAux, min_eq_left h]
      rcases stepStop_eq_or τ (gridPt t n (k+1)) ω with hnew | htop
      · exact Or.inl ⟨k+1, le_rfl, hnew⟩
      · exact Or.inr htop
    · simp only [gridStopAux, min_eq_right (le_of_not_ge h)]
      rcases ih with ⟨j, hj, heq⟩ | htop
      · exact Or.inl ⟨j, hj.trans (Nat.le_succ k), heq⟩
      · exact Or.inr htop

#print axioms solution
