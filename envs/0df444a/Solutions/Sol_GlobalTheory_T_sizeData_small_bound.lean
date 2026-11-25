-- Prove2me | solution 1 for GlobalTheory.T.sizeData_small_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:06:07.568475+00:00
-- url     : https://prove2.me/submissions/acadb021-7dab-47d4-baef-947043d60cc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ParametersSmallBound
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ParametersSmallBoundStatement
import Theorems.Thm_GlobalTheory_FlowParameters_sizeDataSmall


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ParametersSmall := by
  first | exact @GlobalTheory.FlowParameters.sizeDataSmall | exact GlobalTheory.FlowParameters.sizeDataSmall | (intros; apply GlobalTheory.FlowParameters.sizeDataSmall <;> assumption)
end _root_.GlobalTheory.T
