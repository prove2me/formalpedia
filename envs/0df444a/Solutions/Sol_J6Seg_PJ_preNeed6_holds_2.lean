-- Prove2me | solution 2 for J6Seg.PJ.preNeed6_holds
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:33:53.0853+00:00
-- url     : https://prove2.me/submissions/7a7b212f-83a7-48ee-a267-1a92056fe47b

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
