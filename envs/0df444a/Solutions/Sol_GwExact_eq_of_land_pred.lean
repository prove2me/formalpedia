-- Prove2me | solution 1 for GwExact.eq_of_land_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:21.277612+00:00
-- url     : https://prove2.me/submissions/a4f24f34-ec96-406a-ac5b-c1d5125dd793

module
public import Definitions.Def_GwExact_Check

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (x : Nat) : Nat.land x (x - 1) = 0 →
    ∀ u v, x.testBit u = true → x.testBit v = true → u = v := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro hx u v hu hv
    have key : ∀ i, (x &&& (x - 1)).testBit i = false := by
      intro i; have : x &&& (x - 1) = 0 := hx; rw [this]; simp
    have hsucc : ∀ y i, y.testBit (i + 1) = (y / 2).testBit i := fun y i => Nat.testBit_succ y i
    rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2
    · -- x even
      have hy : x / 2 < x := by
        have : x ≠ 0 := by rintro rfl; simp at hu
        omega
      have hy' : Nat.land (x / 2) (x / 2 - 1) = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        have := key (i + 1)
        rw [Nat.testBit_and, hsucc, hsucc, show (x - 1) / 2 = x / 2 - 1 by omega] at this
        show ((x / 2) &&& (x / 2 - 1)).testBit i = Nat.testBit 0 i
        rw [Nat.testBit_and, this]; simp
      have h0 : x.testBit 0 = false := by simp [Nat.testBit_zero, hx2]
      cases u with
      | zero => rw [h0] at hu; exact absurd hu (by simp)
      | succ u =>
        cases v with
        | zero => rw [h0] at hv; exact absurd hv (by simp)
        | succ v =>
          rw [hsucc] at hu hv
          have := ih (x / 2) hy hy' u v hu hv
          omega
    · -- x odd
      have hhalf : x / 2 = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        have := key (i + 1)
        rw [Nat.testBit_and, hsucc, hsucc, show (x - 1) / 2 = x / 2 by omega, Bool.and_self] at this
        simp [this]
      have hsmall : ∀ w, x.testBit w = true → w = 0 := by
        intro w hw
        cases w with
        | zero => rfl
        | succ w => rw [hsucc, hhalf] at hw; simp at hw
      rw [hsmall u hu, hsmall v hv]
end GwExact
