-- Prove2me | solution 1 for Nat.lt_ceilDiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:01.550715+00:00
-- url     : https://prove2.me/submissions/b2890373-9438-4500-b5bd-a6ddd19358bc

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
import Theorems.Thm_Nat_ceilDiv_le_iff

set_option autoImplicit false
section
open Nat
namespace Nat
theorem _root_.solution {a b i : ℕ} (hb : 0 < b) : i < a ⌈/⌉ b ↔ i * b < a := by
  rw [← Nat.not_le, ceilDiv_le_iff hb, Nat.not_le]
end Nat
