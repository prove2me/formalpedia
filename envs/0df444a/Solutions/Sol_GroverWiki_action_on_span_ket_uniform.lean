-- Prove2me | solution 1 for GroverWiki.action_on_span_ket_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T12:59:54.66723+00:00
-- url     : https://prove2.me/submissions/304d1917-188f-48ac-b48d-b4ec7d202bbc

import Mathlib
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) (a b : ℂ) :
    diffusion N *ᵥ (a • ket ω + b • uniformState N) =
        (-a) • ket ω + (2 * a / (Real.sqrt N : ℂ) + b) • uniformState N ∧
      phaseOracle f *ᵥ (a • ket ω + b • uniformState N) =
        (-a - 2 * b / (Real.sqrt N : ℂ)) • ket ω + b • uniformState N := by
  classical
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le ω.val) ω.isLt
  have hs : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hN))
  have hc : (Real.sqrt N : ℂ) ≠ 0 := by exact_mod_cast hs
  have hsq : (Real.sqrt N : ℂ) ^ 2 = (N : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hnorm : (N : ℂ) * (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ = 1 := by
    rw [← hsq]
    field_simp
  have hinner : dotProduct (star (uniformState N))
      (a • ket ω + b • uniformState N) =
      (Real.sqrt N : ℂ)⁻¹ * a + b := by
    have hstar : star (uniformState N) = uniformState N := by
      ext j
      simp [uniformState]
    rw [hstar]
    simp [dotProduct, uniformState, ket, Pi.single_apply, mul_add, mul_ite,
      Finset.sum_add_distrib, Complex.ofReal_inv, ← mul_assoc]
    linear_combination b * hnorm
  constructor
  · rw [diffusion, sub_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, hinner]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, uniformState,
      Complex.ofReal_inv, div_eq_mul_inv, op_smul_eq_mul]
    ring
  · ext i
    by_cases hi : i = ω
    · subst i
      have hf : f ω = 1 := (hω ω).2 rfl
      simp [phaseOracle, mulVec_diagonal, hf, ket, uniformState, div_eq_mul_inv]
      ring
    · have hf : f i = 0 := by
        have hn : f i ≠ 1 := fun he => hi ((hω i).1 he)
        apply Fin.ext
        have hv := (f i).isLt
        have hnval : (f i).val ≠ 1 := by
          intro he
          apply hn
          apply Fin.ext
          exact he
        change (f i).val = 0
        omega
      simp [phaseOracle, mulVec_diagonal, hf, ket, uniformState, hi, Ne.symm hi]
