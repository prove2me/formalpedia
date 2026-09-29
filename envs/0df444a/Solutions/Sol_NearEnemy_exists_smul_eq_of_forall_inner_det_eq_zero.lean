-- Prove2me | solution 1 for NearEnemy.exists_smul_eq_of_forall_inner_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:35.556919+00:00
-- url     : https://prove2.me/submissions/e1d331b7-8cf2-406b-b597-e7a8bbaf7305

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy

open NearEnemy in
theorem solution {v w : V}
    (h : ∀ p q : V, ⟪p, v⟫ * ⟪q, w⟫ - ⟪p, w⟫ * ⟪q, v⟫ = 0) :
    (∃ t : ℝ, w = t • v) ∨ (∃ t : ℝ, v = t • w) := by
  by_cases hv : v = 0
  · exact Or.inr ⟨0, by simp [hv]⟩
  · left
    have hvv : ⟪v, v⟫ ≠ 0 := inner_self_ne_zero.mpr hv
    set u : V := ⟪v, v⟫ • w - ⟪v, w⟫ • v with hu
    have expand : ∀ x : V, ⟪x, u⟫ = ⟪v, v⟫ * ⟪x, w⟫ - ⟪v, w⟫ * ⟪x, v⟫ := by
      intro x
      rw [hu, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
    have huv : ⟪u, v⟫ = 0 := by
      rw [real_inner_comm, expand v]
      ring
    have huw : ⟪u, w⟫ = 0 := by
      have hpq := h v u
      rw [huv, mul_zero, sub_zero] at hpq
      rcases mul_eq_zero.mp hpq with h' | h'
      · exact absurd h' hvv
      · exact h'
    have huu : ⟪u, u⟫ = 0 := by
      rw [expand u, huv, huw, mul_zero, mul_zero, sub_zero]
    have hu0 : u = 0 := inner_self_eq_zero.mp huu
    rw [hu, sub_eq_zero] at hu0
    refine ⟨⟪v, v⟫⁻¹ * ⟪v, w⟫, ?_⟩
    rw [mul_smul, ← hu0, inv_smul_smul₀ hvv]
