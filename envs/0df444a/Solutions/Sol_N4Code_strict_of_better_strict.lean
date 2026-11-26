-- Prove2me | solution 1 for N4Code.strict_of_better_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:00.935523+00:00
-- url     : https://prove2.me/submissions/91549a75-6d3f-4c21-9462-b9dc953dd3fb

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
theorem _root_.solution {n : ℕ} (C₁ C₂ C₃ : Code n)
    (h12 : UniversalBetter C₁ C₂) (h23 : UniversalStrictBetter C₂ C₃) :
    UniversalStrictBetter C₁ C₃ := by
  intro ε hε0 hε1
  exact lt_of_lt_of_le (h23 ε hε0 hε1) (h12 ε hε0 hε1)
end N4Code
