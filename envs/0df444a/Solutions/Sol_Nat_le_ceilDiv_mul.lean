-- Prove2me | solution 1 for Nat.le_ceilDiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:09.896188+00:00
-- url     : https://prove2.me/submissions/604dec79-f531-4b78-a040-e8c69aa86d57

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
import Theorems.Thm_Nat_ceilDiv_le_iff

set_option autoImplicit false
section
open Nat
namespace Nat
theorem _root_.solution {a b : ℕ} (hb : 0 < b) : a ≤ a ⌈/⌉ b * b :=
  (ceilDiv_le_iff hb).1 le_rfl
end Nat
