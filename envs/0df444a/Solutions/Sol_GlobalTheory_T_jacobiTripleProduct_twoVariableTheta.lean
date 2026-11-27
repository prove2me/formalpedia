-- Prove2me | solution 1 for GlobalTheory.T.jacobiTripleProduct_twoVariableTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:57:40.131942+00:00
-- url     : https://prove2.me/submissions/5b641af1-ef53-457e-aee8-ccc5a3ff6ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleProductTwoVariableTheta
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleProductTwoVariableThetaStatement
import Theorems.Thm_GlobalTheory_JacobiTriple_tripleProduct


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  first | exact @GlobalTheory.JacobiTriple.tripleProduct | exact GlobalTheory.JacobiTriple.tripleProduct | (intros; apply GlobalTheory.JacobiTriple.tripleProduct <;> assumption)
end _root_.GlobalTheory.T
