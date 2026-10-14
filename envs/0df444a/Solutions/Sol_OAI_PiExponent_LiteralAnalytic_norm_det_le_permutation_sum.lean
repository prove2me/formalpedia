-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.norm_det_le_permutation_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T12:39:39.582754+00:00
-- url     : https://prove2.me/submissions/7d0dbd3a-8c8b-4490-83c3-2d79d76a79a9

import Mathlib.Tactic

open scoped BigOperators

theorem solution
    {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) :
    ‖M.det‖ ≤ ∑ σ : Equiv.Perm α, ∏ i : α, ‖M i (σ i)‖ := by
  rw [Matrix.det_apply']
  have hsign (σ : Equiv.Perm α) : ‖(Equiv.Perm.sign σ : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast Equiv.Perm.sign_abs σ
  calc
    ‖∑ σ : Equiv.Perm α, (Equiv.Perm.sign σ : ℂ) * ∏ i : α, M (σ i) i‖
        ≤ ∑ σ : Equiv.Perm α,
            ‖(Equiv.Perm.sign σ : ℂ) * ∏ i : α, M (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm α, ∏ i : α, ‖M (σ i) i‖ := by
      simp_rw [norm_mul, hsign, one_mul, norm_prod]
    _ = ∑ σ : Equiv.Perm α, ∏ i : α, ‖M i (σ i)‖ := by
      rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm α))]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Equiv.inv_apply]
      simpa using
        (Equiv.prod_comp σ (fun i => ‖M (σ⁻¹ i) i‖)).symm