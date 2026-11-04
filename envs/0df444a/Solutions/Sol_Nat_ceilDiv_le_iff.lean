-- Prove2me | solution 1 for Nat.ceilDiv_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:05.767184+00:00
-- url     : https://prove2.me/submissions/c569e267-b994-49f3-9db6-ee185dd770a9

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil

set_option autoImplicit false
section
open Nat
namespace Nat
theorem _root_.solution {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by
  rw [ceilDiv_le_iff_le_mul hb, Nat.mul_comm]
end Nat
