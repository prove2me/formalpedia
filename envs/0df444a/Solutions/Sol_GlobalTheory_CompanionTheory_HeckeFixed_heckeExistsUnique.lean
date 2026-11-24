-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:11.351874+00:00
-- url     : https://prove2.me/submissions/a388c678-22e7-4da9-a7f5-b5517d89108c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_LocalBaseChange_TwistedIndependenceLemma_TwistedIndependence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeCharacterExistsUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_existsUnique_isHeckeOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeFixed
namespace GlobalTheory.CompanionTheory.HeckeFixed
theorem _root_.solution : PositivityTheory.Lbc.HeckeExistsUnique := by
  intro G _ _ _ K _ hKc V _ _ π hπ g
  exact existsUnique_isHeckeOn hπ hKc g
end GlobalTheory.CompanionTheory.HeckeFixed
