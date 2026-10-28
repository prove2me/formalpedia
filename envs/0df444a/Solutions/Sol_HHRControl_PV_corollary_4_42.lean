-- Prove2me | solution 1 for HHRControl.PV.corollary_4_42
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:02:55.188885+00:00
-- url     : https://prove2.me/submissions/acae19e6-011a-4710-b2fa-305543476af4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Theorems.Thm_CookPvsNP_npComplete_of_polyReducible
import Theorems.Thm_HHRControl_PV_example_4_16
import Theorems.Thm_HHRControl_PV_theorem_4_39
import Theorems.Thm_HHRControl_PV_plurality_tp_in_NP
import Theorems.Thm_HHRControl_PV_restrictedHS_polyReducible_plurality_tp

set_option autoImplicit false

open HHRControl.PV CookPvsNP

theorem solution (hHS : NPComplete hittingSetLang) :
    ResistantCC .TP plurality ∧ ResistantDC .TP plurality :=
  ⟨⟨example_4_16.2.2.1,
    npComplete_of_polyReducible restrictedHSLang (ccLang .TP plurality)
      (theorem_4_39 hHS) plurality_tp_in_NP.1 restrictedHS_polyReducible_plurality_tp.1⟩,
   ⟨example_4_16.2.2.2,
    npComplete_of_polyReducible restrictedHSLang (dcLang .TP plurality)
      (theorem_4_39 hHS) plurality_tp_in_NP.2 restrictedHS_polyReducible_plurality_tp.2⟩⟩
