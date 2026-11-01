-- Prove2me | solution 2 for HHRControl.PV.theorem_4_46
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T13:14:48.838766+00:00
-- url     : https://prove2.me/submissions/30f0b8ae-1f89-4ce5-bba6-12d158d8aad3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_HHRControl_PV_example_4_17
import Theorems.Thm_HHRControl_PV_approval_cc_in_NP
import Theorems.Thm_HHRControl_PV_x3c_polyReducible_approval_cc_te

open HHRControl.PV CookPvsNP

theorem solution (hX3C : NPComplete x3cLang) : ResistantCC .TE approval :=
  ⟨example_4_17.2.1,
   npComplete_of_polyReducible x3cLang (ccLang .TE approval) hX3C (approval_cc_in_NP .TE)
     x3c_polyReducible_approval_cc_te⟩
