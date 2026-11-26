-- Prove2me | solution 1 for N4Code.r_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:21.187252+00:00
-- url     : https://prove2.me/submissions/75214194-a279-448a-83a9-1af274d67c5f

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {ε : ℝ} (hε1 : ε < 1 / 2) : ε / (1 - ε) < 1 := by
  have h1 : 0 < 1 - ε := by linarith
  exact (div_lt_one h1).mpr (by linarith)
end N4Code
