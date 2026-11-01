-- Prove2me | solution 2 for HHRControl.PV.theorem_4_39
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:14:46.802853+00:00
-- url     : https://prove2.me/submissions/989c4300-ee64-4189-8d41-f5549aee776a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_HHRControl_PV_restrictedHS_in_NP
import Theorems.Thm_HHRControl_PV_hittingSet_polyReducible_restrictedHS

open HHRControl.PV CookPvsNP

theorem solution (hHS : NPComplete hittingSetLang) : NPComplete restrictedHSLang :=
  npComplete_of_polyReducible hittingSetLang restrictedHSLang hHS restrictedHS_in_NP
    hittingSet_polyReducible_restrictedHS
