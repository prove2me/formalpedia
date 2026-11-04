-- Prove2me | solution 1 for Nat.ceilDiv_mul_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:11.449679+00:00
-- url     : https://prove2.me/submissions/452cc190-7ef1-445d-ac61-76b91798a032

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil

set_option autoImplicit false
section
open Nat
namespace Nat
theorem _root_.solution {a b : ℕ} (hb : 0 < b) : a ⌈/⌉ b * b < a + b := by
  have := Nat.div_mul_le_self (a + b - 1) b
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega
end Nat
