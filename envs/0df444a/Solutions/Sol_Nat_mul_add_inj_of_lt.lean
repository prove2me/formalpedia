-- Prove2me | solution 1 for Nat.mul_add_inj_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:54.648532+00:00
-- url     : https://prove2.me/submissions/01abf340-78cb-4984-985d-9ff3204b9552

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Theorems.Thm_Nat_mul_add_div_of_lt

set_option autoImplicit false
public section
open Nat
namespace Nat
theorem _root_.solution {a b a' b' n : ℕ} (hb : b < n) (hb' : b' < n)
    (h : a * n + b = a' * n + b') :
    a = a' ∧ b = b' :=
  ⟨by rw [← mul_add_div_of_lt (a := a) hb, h, mul_add_div_of_lt hb'],
    by rw [← Nat.mul_add_mod_of_lt (a := a) hb, h, Nat.mul_add_mod_of_lt hb']⟩
end Nat
