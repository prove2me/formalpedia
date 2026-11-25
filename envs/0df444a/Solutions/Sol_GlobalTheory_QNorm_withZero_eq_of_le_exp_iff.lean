-- Prove2me | solution 1 for GlobalTheory.QNorm.withZero_eq_of_le_exp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:06:07.240894+00:00
-- url     : https://prove2.me/submissions/fd12eea7-5f9e-4902-9f99-b6b08cce11e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have key : ∀ a b : ℤᵐ⁰, b ≠ 0 → b ≤ 1 →
      (∀ n : ℕ, b ≤ WithZero.exp (-(n : ℤ)) → a ≤ WithZero.exp (-(n : ℤ))) → a ≤ b := by
    intro a b hb0 hb h
    have e : b = WithZero.exp (WithZero.log b) := (WithZero.exp_log hb0).symm
    have hl : WithZero.log b ≤ 0 := by
      rw [e, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb; exact hb
    have e2 : WithZero.log b = -(((-WithZero.log b).toNat : ℕ) : ℤ) := by omega
    rw [e2] at e
    rw [e]
    exact h _ e.le
  have key0 : ∀ a : ℤᵐ⁰, (∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ))) → a = 0 := by
    intro a h
    by_contra ha0
    have e : a = WithZero.exp (WithZero.log a) := (WithZero.exp_log ha0).symm
    have := h ((-WithZero.log a).toNat + 1)
    rw [e, WithZero.exp_le_exp, WithZero.log_exp] at this
    omega
  by_cases hb0 : b = 0
  · subst hb0
    exact key0 a fun n => (h n).2 (by simp)
  by_cases ha0 : a = 0
  · subst ha0
    exact (key0 b fun n => (h n).1 (by simp)).symm
  exact le_antisymm (key a b hb0 hb fun n => (h n).2) (key b a ha0 ha fun n => (h n).1)
end GlobalTheory.QNorm
