-- Prove2me | solution 1 for N4Code.weight_lt_of_dist_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:44.700017+00:00
-- url     : https://prove2.me/submissions/28df706e-2c8e-4bbf-ab56-60884d0aded9

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_weight_strictAnti

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {a b : ℕ} (h : a < b) :
    (1 - ε) ^ (n - b) * ε ^ b < (1 - ε) ^ (n - a) * ε ^ a :=
  weight_strictAnti hε0 hε1 h
end N4Code
