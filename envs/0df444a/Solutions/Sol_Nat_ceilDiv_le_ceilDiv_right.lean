-- Prove2me | solution 1 for Nat.ceilDiv_le_ceilDiv_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:12.77577+00:00
-- url     : https://prove2.me/submissions/a60c1678-e7bd-4d94-9969-38bdb68ce975

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil

set_option autoImplicit false
section
open Nat
namespace Nat
theorem _root_.solution {a a' : ℕ} (h : a ≤ a') (b : ℕ) : a ⌈/⌉ b ≤ a' ⌈/⌉ b :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h b) 1)
end Nat
