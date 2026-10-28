-- Prove2me | solution 1 for HHRControl.PV.theorem_3_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:30:20.169652+00:00
-- url     : https://prove2.me/submissions/467a8c96-200d-4243-b594-c3991b29f04a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Theorems.Thm_HHRControl_PV_theorem_4_46
import Theorems.Thm_HHRControl_PV_theorem_4_45
import Theorems.Thm_HHRControl_PV_theorem_4_21
import Theorems.Thm_HHRControl_PV_theorem_4_18
import Theorems.Thm_HHRControl_PV_theorem_4_19
import Theorems.Thm_HHRControl_PV_corollary_4_42
import Theorems.Thm_HHRControl_PV_theorem_4_20

open HHRControl.PV CookPvsNP

theorem solution (hHS : NPComplete hittingSetLang) (hX3C : NPComplete x3cLang) :
    ResistantCC .TE approval ∧ ResistantCC .TP approval ∧
    (VulnerableDC .TE approval ∧ CertVulnerableDC .TE approval) ∧
    (VulnerableDC .TP approval ∧ CertVulnerableDC .TP approval) ∧
    (VulnerableCC .TE plurality ∧ CertVulnerableCC .TE plurality) ∧
    (VulnerableDC .TE plurality ∧ CertVulnerableDC .TE plurality) ∧
    ResistantCC .TP plurality ∧ ResistantDC .TP plurality ∧
    ∀ rule : TieRule, VulnerableDC rule condorcet ∧ CertVulnerableDC rule condorcet :=
  ⟨theorem_4_46 hX3C, theorem_4_45 hX3C, theorem_4_21.1, theorem_4_21.2,
   theorem_4_18, theorem_4_19, (corollary_4_42 hHS).1, (corollary_4_42 hHS).2,
   theorem_4_20⟩
