-- Prove2me | solution 1 for N4Code.r_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:12.461926+00:00
-- url     : https://prove2.me/submissions/fcc21993-fd51-4d09-a97b-09f377f786c5

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) : 0 < ε / (1 - ε) := by
  have h1 : 0 < 1 - ε := by linarith
  positivity
end N4Code
