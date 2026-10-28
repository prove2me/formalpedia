-- Prove2me | solution 2 for J6Seg.ATab.preA6
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:39:03.262+00:00
-- url     : https://prove2.me/submissions/acebe71a-23d0-4b1b-b133-8f75a7f3529d

import Definitions.Def_IntMul_Kappa_R6_Defs69
import Theorems.Thm_J6Seg_ATab_numA6
import Theorems.Thm_J6Seg_ATab_preA6_of_num

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg J6Seg.ATab
open IntMul.Kappa.R6
open NLogN

/-- `PreA6` follows from the published numeric witness `numA6` via `preA6_of_num`. -/
theorem solution (P : Prm) (hP : P.Ok) (pkA pkC bA bC : ℕ)
    (tab : Fin 1 → IStmt HS 1) : PreA6 P pkA pkC bA bC tab :=
  preA6_of_num (numA6 P hP pkA pkC bA bC) tab
