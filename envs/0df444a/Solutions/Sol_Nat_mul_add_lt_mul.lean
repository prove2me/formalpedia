-- Prove2me | solution 1 for Nat.mul_add_lt_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:13.453005+00:00
-- url     : https://prove2.me/submissions/37fde6e4-d377-4d0c-8d64-51fce222dc52

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index

set_option autoImplicit false
public section
open Nat
namespace Nat
theorem _root_.solution {a b m n : ℕ} (ha : a < m) (hb : b < n) : a * n + b < m * n :=
  Nat.mul_comm a n ▸ Nat.mul_add_lt_mul_of_lt_of_lt ha hb
end Nat
