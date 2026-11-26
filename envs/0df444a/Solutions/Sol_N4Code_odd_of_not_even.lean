-- Prove2me | solution 1 for N4Code.odd_of_not_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:13:22.046576+00:00
-- url     : https://prove2.me/submissions/e80d7dfa-887d-43fd-9315-fe7f56eb457d

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
theorem _root_.solution {n : ℕ} (h : ¬ Even n) : Odd n := by
  rwa [← Nat.not_even_iff_odd]
end N4Code
