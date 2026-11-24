-- Prove2me | solution 1 for GlobalTheory.T.fraction_exists_of_smith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:39.82341+00:00
-- url     : https://prove2.me/submissions/d2d83731-f9ff-4771-8f26-4e28504ee1e2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_FractionExistsOfSmith
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_FractionExistsOfSmithStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_fracExists_of_smith


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Smith → FracExists := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith | exact GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith | (intros; apply GlobalTheory.CompanionTheory.InertZeta.fracExists_of_smith <;> assumption)
end _root_.GlobalTheory.T
