-- Prove2me | solution 1 for Nat.mul_add_div_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:15.398655+00:00
-- url     : https://prove2.me/submissions/958a53a7-97a9-445e-a38b-1b09e26bbb6a

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index

set_option autoImplicit false
public section
open Nat
namespace Nat
theorem _root_.solution {a b n : ℕ} (hb : b < n) : (a * n + b) / n = a := by
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hb), Nat.div_eq_of_lt hb, Nat.add_zero]
end Nat
