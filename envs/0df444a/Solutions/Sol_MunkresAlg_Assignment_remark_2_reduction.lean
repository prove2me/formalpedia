-- Prove2me | solution 1 for MunkresAlg.Assignment.remark_2_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:14:13.950882+00:00
-- url     : https://prove2.me/submissions/eb576d75-2323-4b00-9c33-913959c06b8c

import Mathlib
import Definitions.Def_HeldWolfeCrowder_Assignment_Setting



namespace MunkresAlg.Assignment

theorem r2_core {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    HeldWolfeCrowder.Assignment.IsOptimalAssignment A σ ↔
      HeldWolfeCrowder.Assignment.IsOptimalAssignment (fun i j => A i j - u i - v j) σ := by
  have key : ∀ τ : Equiv.Perm (Fin n),
      HeldWolfeCrowder.Assignment.assignCost (fun i j => A i j - u i - v j) τ =
      HeldWolfeCrowder.Assignment.assignCost A τ - ∑ i, u i - ∑ j, v j := by
    intro τ
    unfold HeldWolfeCrowder.Assignment.assignCost
    simp only [Finset.sum_sub_distrib]
    have : ∑ r, u (τ r) = ∑ i, u i := Equiv.sum_comp τ u
    rw [this]
  unfold HeldWolfeCrowder.Assignment.IsOptimalAssignment
  constructor
  · intro h τ
    rw [key, key]
    have := h τ
    linarith
  · intro h τ
    have := h τ
    rw [key, key] at this
    linarith

end MunkresAlg.Assignment

open MunkresAlg.Assignment


theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) :
    HeldWolfeCrowder.Assignment.IsOptimalAssignment A σ ↔
      HeldWolfeCrowder.Assignment.IsOptimalAssignment (fun i j => A i j - u i - v j) σ := by
  exact r2_core A u v σ
