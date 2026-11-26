-- Prove2me | solution 1 for N4Code.dCode_eq_min_dO_dP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:09.944331+00:00
-- url     : https://prove2.me/submissions/3fe5575a-4c6a-4697-958c-f6ec0f8e3c0b

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (y : Word n) :
    dCode C y = min (dO C y) (dP C y) := by
  unfold dCode dO dP
  omega
end N4Code
