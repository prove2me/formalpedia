-- Prove2me | solution 1 for GlobalTheory.ThetaWeberObj.thetaWeberStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:05:23.904467+00:00
-- url     : https://prove2.me/submissions/964ed7a6-ff29-4ddf-9c4d-2bcd57ccfe7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiProductOfThetaWeber
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaWeberStatement
import Theorems.Thm_Formalism_L2_Th1_F_sgStarAdd
import Theorems.Thm_Formalism_L2_Th1_F_sgStarBasic
import Theorems.Thm_Formalism_L2_Th1_F_thetaLine
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_thetaWeberStatement_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ThetaWeberObj
namespace GlobalTheory.ThetaWeberObj
theorem _root_.solution : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeberStatement :=
  GlobalTheory.ThetaWeberRoad.thetaWeberStatement_of Formalism.L2.Th1.F.thetaLine Formalism.L2.Th1.F.sgStarBasic
    Formalism.L2.Th1.F.sgStarAdd
end GlobalTheory.ThetaWeberObj
