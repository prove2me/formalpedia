-- Prove2me | solution 1 for GlobalTheory.T.hecke_character_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:23:22.580691+00:00
-- url     : https://prove2.me/submissions/1c290787-6202-49a0-9ab5-81862412698f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeCharacterExistsUnique
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_LocalBaseChange_TwistedIndependenceLemma_TwistedIndependence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeCharacterExistsUniqueStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_heckeExistsUnique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : PositivityTheory.Lbc.HeckeExistsUnique := by
  first | exact @GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | exact GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | (intros; apply GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique <;> assumption)
end _root_.GlobalTheory.T
