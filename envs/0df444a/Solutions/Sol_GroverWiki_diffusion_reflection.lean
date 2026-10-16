-- Prove2me | solution 1 for GroverWiki.diffusion_reflection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:04:20.069552+00:00
-- url     : https://prove2.me/submissions/8e26c5a0-be49-4f2e-9216-1ce1351d48a5

import Mathlib
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution (N : ℕ) :
    diffusion N *ᵥ uniformState N = uniformState N ∧
      ∀ v : Fin N → ℂ, star (uniformState N) ⬝ᵥ v = 0 → diffusion N *ᵥ v = -v := by
  classical
  constructor
  · by_cases hN : N = 0
    · subst N
      ext i
      exact Fin.elim0 i
    · have hs : Real.sqrt (N : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hN))
      have hc : (Real.sqrt N : ℂ) ≠ 0 := by exact_mod_cast hs
      have hsq : (Real.sqrt N : ℂ) ^ 2 = (N : ℂ) := by
        exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      have hnorm : (N : ℂ) * (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ = 1 := by
        rw [← hsq]
        field_simp
      have hinner : star (uniformState N) ⬝ᵥ uniformState N = 1 := by
        simp [dotProduct, uniformState, Complex.ofReal_inv, ← mul_assoc, hnorm]
      rw [diffusion, sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, hinner]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
      ring
  · intro v hv
    rw [diffusion, sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, hv]
    simp
