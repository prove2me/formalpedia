-- Prove2me | solution 1 for N4Code.classIII_count1_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:36.44124+00:00
-- url     : https://prove2.me/submissions/36a6d580-f6d1-4de4-ba62-f4953b047a97

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (h : ClassIII C) : count C 1 > 0 := by
  rcases h.2 with h | h
  · omega
  · omega
end N4Code
