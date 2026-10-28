-- Prove2me | solution 1 for HHRControl.PV.theorem_4_39
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:02:55.846265+00:00
-- url     : https://prove2.me/submissions/58d007c4-17de-4549-a7c3-2c18ad3dbdd1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_HHRControl_PV_restrictedHS_in_NP
import Theorems.Thm_HHRControl_PV_hittingSet_polyReducible_restrictedHS

set_option autoImplicit false

open HHRControl.PV CookPvsNP

theorem solution (hHS : NPComplete hittingSetLang) : NPComplete restrictedHSLang :=
  npComplete_of_polyReducible hittingSetLang restrictedHSLang
    hHS restrictedHS_in_NP hittingSet_polyReducible_restrictedHS
