-- Prove2me | solution 1 for MohP3.comp_X8_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:19.996999+00:00
-- url     : https://prove2.me/submissions/83900fb8-77f1-4e5b-91d7-3e55c0210701

module
public import Mathlib
public import Definitions.Def_MohP3_Independence

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3
namespace MohP3
theorem _root_.solution (p : ℚ[X]) (n : ℕ) (hn : ¬ (8 ∣ n)) : (p.comp (X^8)).coeff n = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq]
  | monomial k a =>
      rw [Polynomial.monomial_comp, ← pow_mul, coeff_C_mul, coeff_X_pow]
      have : n ≠ 8*k := by rintro rfl; exact hn ⟨k, rfl⟩
      simp [this]
end MohP3
