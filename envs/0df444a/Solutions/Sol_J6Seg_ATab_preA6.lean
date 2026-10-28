-- Prove2me | solution 1 for J6Seg.ATab.preA6
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:38:03.723254+00:00
-- url     : https://prove2.me/submissions/a0037605-ad4c-45a9-81b3-d3117738ee00

import Definitions.Def_IntMul_Kappa_R6_Defs69
import Theorems.Thm_J6Seg_ATab_numA6
import Theorems.Thm_J6Seg_ATab_preA6_of_num

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg J6Seg.ATab
open IntMul.Kappa.R6
open NLogN

/-- `PreA6` in the round-six regime is `preA6_of_num` applied to the proved `numA6`. -/
theorem solution (P : Prm) (hP : P.Ok) (pkA pkC bA bC : ℕ) (tab : Fin 1 → IStmt HS 1) :
    PreA6 P pkA pkC bA bC tab :=
  preA6_of_num (numA6 P hP pkA pkC bA bC) tab
