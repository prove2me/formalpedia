-- Prove2me | solution 1 for GlobalTheory.card_finMulAntidiag_eq_zeta_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:40.375662+00:00
-- url     : https://prove2.me/submissions/74b45c64-73d4-452f-b437-413f905836be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k n : ℕ) :
    (Nat.finMulAntidiag k n).card = (ζ ^ k : ArithmeticFunction ℕ) n := by
  induction k generalizing n with
  | zero =>
    by_cases h : n = 1
    · subst h; simp [Nat.finMulAntidiag_one]
    · simp [Nat.finMulAntidiag_zero_left h, ArithmeticFunction.one_apply_ne h]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.mul_apply]
    have : ∑ x ∈ n.divisorsAntidiagonal, (ζ : ArithmeticFunction ℕ) x.1 * (ζ ^ k : ArithmeticFunction ℕ) x.2
        = ∑ x ∈ n.divisorsAntidiagonal, (Nat.finMulAntidiag k x.2).card := by
      refine sum_congr rfl fun x hx => ?_
      rw [ArithmeticFunction.zeta_apply_ne (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx),
        one_mul, ih]
    rw [this, ← card_sigma]
    refine card_nbij' (fun f => ⟨(f 0, ∏ i, f (Fin.succ i)), fun i => f (Fin.succ i)⟩)
      (fun y => Fin.cons y.1.1 y.2) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [mem_coe, Nat.mem_finMulAntidiag, Fin.prod_univ_succ] at hf
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag]
      refine ⟨hf, trivial, ?_⟩
      intro h
      exact hf.2 (by rw [← hf.1, h, mul_zero])
    · rintro ⟨⟨a, b⟩, g⟩ hy
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hy
      simp only [mem_coe, Nat.mem_finMulAntidiag, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [hy.2.1]; exact hy.1
    · intro f _
      exact Fin.cons_self_tail f
    · rintro ⟨⟨a, b⟩, g⟩ hy
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hy
      simp only [Fin.cons_zero, Fin.cons_succ, hy.2.1]
end GlobalTheory
