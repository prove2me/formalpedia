-- Prove2me | solution 1 for N4Code.div_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:48.814537+00:00
-- url     : https://prove2.me/submissions/d98f242a-7b04-4caf-aa61-87441f0921b2

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n k : ℕ} (h : n = 2 * k) : n / 2 = k := by
  rw [h]
  exact Nat.mul_div_right k (by decide : 0 < 2)
end N4Code
