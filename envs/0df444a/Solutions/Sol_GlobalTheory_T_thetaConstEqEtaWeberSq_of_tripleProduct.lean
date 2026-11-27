-- Prove2me | solution 1 for GlobalTheory.T.thetaConstEqEtaWeberSq_of_tripleProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:38:09.103048+00:00
-- url     : https://prove2.me/submissions/30196b5d-951e-4465-8681-a0cc2525960c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaConstEqEtaWeberSqOfTripleProduct
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaConstEqEtaWeberSqOfTripleProductStatement
import Theorems.Thm_GlobalTheory_ThetaWeberProof_thetaWeber_of_tripleProduct


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
theorem _root_.solution : GlobalTheory.ThetaWeberRoad.TripleProduct → ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ := by
  first | exact @GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct | exact GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct | (intros; apply GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct <;> assumption)
end _root_.GlobalTheory.T
