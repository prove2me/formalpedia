-- Prove2me | solution 1 for GlobalTheory.SmGL.FinitenessModel.padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:08.298093+00:00
-- url     : https://prove2.me/submissions/71f373b7-f7dc-4698-b797-b02ba7b98da9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfFiniteDimensional
import Theorems.Thm_GlobalTheory_SplitWeil_Model_padic_localField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.FinitenessModel
namespace GlobalTheory.SmGL.FinitenessModel
theorem _root_.solution (h : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (p : ℕ) [Fact p.Prime] :
    IrreducibleAdmissible ℚ_[p] :=
  haveI := GlobalTheory.SplitWeil.Model.padic_localField p
  (h ℚ_[p]).1
end GlobalTheory.SmGL.FinitenessModel
