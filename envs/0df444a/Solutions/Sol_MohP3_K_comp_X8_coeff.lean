-- Prove2me | solution 1 for MohP3.K.comp_X8_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:25:26.532705+00:00
-- url     : https://prove2.me/submissions/21c3013c-6184-49ef-8e56-c16a3ed845e9

module
public import Mathlib
public import Definitions.Def_MohP3_IndependenceK

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3 MohP3.K
variable (k : Type*) [Field k]
variable {k}
namespace MohP3.K
theorem _root_.solution (p : Polynomial k) (n : ℕ) (hn : ¬ (8 ∣ n)) : (p.comp (X ^ 8)).coeff n = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq]
  | monomial m a =>
      rw [Polynomial.monomial_comp, ← pow_mul, coeff_C_mul, coeff_X_pow]
      have : n ≠ 8 * m := by rintro rfl; exact hn ⟨m, rfl⟩
      simp [this]
end MohP3.K
