-- Prove2me | solution 1 for GlobalTheory.T.multiplicativity_infinite_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:24:32.233521+00:00
-- url     : https://prove2.me/submissions/e58f7a60-f2a8-4e2a-939f-16c8a2428ef2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityInfinitePlaces
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityInfinitePlacesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_GramWedge_mulI_of_detMono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : DetMono → MulI := by
  first | exact @GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | exact GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | (intros; apply GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono <;> assumption)
end _root_.GlobalTheory.T
