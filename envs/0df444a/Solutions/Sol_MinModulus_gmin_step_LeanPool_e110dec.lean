-- Prove2me | solution 1 for MinModulus.gmin_step_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:06.997557+00:00
-- url     : https://prove2.me/submissions/c182207b-3f55-4e62-ae9c-74d52e2c07a8

module
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_UniqueSums
public import Theorems.Thm_MinModulus_gmin_add_pow_LeanPool_e110dec

set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset
namespace MinModulus
theorem _root_.solution : ∀ w t M M', t ≤ w → M' + 2 ^ t = M + 2 ^ (w + 1) →
    gmin w M + 1 ≤ gmin w M' := by
  intro w
  induction w with
  | zero =>
    intro t M M' ht hM
    have ht0 : t = 0 := by omega
    subst ht0
    norm_num at hM
    simp only [gmin]
    omega
  | succ w ih =>
    intro t M M' ht hM
    have h2 : 2 ^ (w + 1 + 1) = 2 * 2 ^ (w + 1) := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ (w + 1) := Nat.one_le_pow _ _ (by norm_num)
    simp only [gmin]
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · -- gap `2^{w+2} − 1`: the parity flips
      simp only [pow_zero] at hM
      rcases Nat.mod_two_eq_zero_or_one M with hp | hp
      · -- `M` even, `M'` odd: recurse on the `(w, 0)` instance
        have hstep := ih 0 (M / 2) (M' / 2) (Nat.zero_le w)
          (by simp only [pow_zero]; omega)
        omega
      · -- `M` odd, `M'` even: `M'/2 = M/2 + 2·2^w`, two top coins
        have ha1 := gmin_add_pow_LeanPool_e110dec w (M / 2)
        have ha2 := gmin_add_pow_LeanPool_e110dec w (M / 2 + 2 ^ w)
        have h2w : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
        have e2 : M' / 2 = M / 2 + 2 ^ w + 2 ^ w := by omega
        rw [e2, ha2, ha1]
        omega
    · -- gap `2^{w+2} − 2^t` with `t ≥ 1`: parities agree, recurse on `(w, t−1)`
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hps : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
      have hstep := ih s (M / 2) (M' / 2) (by omega) (by omega)
      omega
end MinModulus
