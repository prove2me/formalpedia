-- Prove2me | solution 1 for Nat.ceil_div_eq_ceilDiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:04:14.052404+00:00
-- url     : https://prove2.me/submissions/350f98d4-1936-4178-8d58-26a54f3d4dcd

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Ceil
import Theorems.Thm_Nat_ceilDiv_le_iff

set_option autoImplicit false
section
open Nat
namespace Nat
theorem _root_.solution (a : ℕ) {b : ℕ} (hb : 0 < b) : ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by
  refine eq_of_forall_ge_iff fun k => ?_
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.2 hb), ceilDiv_le_iff hb]
  exact_mod_cast Iff.rfl
end Nat
