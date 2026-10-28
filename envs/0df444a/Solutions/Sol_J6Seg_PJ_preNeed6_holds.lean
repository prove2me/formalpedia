-- Prove2me | solution 1 for J6Seg.PJ.preNeed6_holds
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:33:34.841235+00:00
-- url     : https://prove2.me/submissions/3eed8a88-7937-423b-8930-4a1d0ef8e030

import Definitions.Def_IntMul_Kappa_R6_Defs66
import Theorems.Thm_J6Seg_PJ_preU6_holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

open J6Seg J6Seg.PJ
open IntMul.Kappa.R6

/-- `PreNeed6` is `PreU6` under the unused `LineNeed6` table hypotheses;
`preU6_holds` already gives `PreU6` for every table. -/
theorem solution (P : Prm) (hP : P.Ok) (pl : Plan6) : PreNeed6 P pl :=
  fun tab _ _ _ => preU6_holds P hP pl tab
