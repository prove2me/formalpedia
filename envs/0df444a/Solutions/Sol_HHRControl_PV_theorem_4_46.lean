-- Prove2me | solution 1 for HHRControl.PV.theorem_4_46
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:02:57.159107+00:00
-- url     : https://prove2.me/submissions/e2f6f109-dd12-4f8a-8a38-7b0e7c283817
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_HHRControl_PV_example_4_17
import Theorems.Thm_HHRControl_PV_approval_cc_in_NP
import Theorems.Thm_HHRControl_PV_x3c_polyReducible_approval_cc_te

set_option autoImplicit false

open HHRControl.PV CookPvsNP

theorem solution (hX3C : NPComplete x3cLang) : ResistantCC .TE approval :=
  ⟨example_4_17.2.1,
   npComplete_of_polyReducible x3cLang (ccLang .TE approval)
     hX3C (approval_cc_in_NP .TE) x3c_polyReducible_approval_cc_te⟩
