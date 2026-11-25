-- Prove2me | solution 1 for GlobalTheory.T.pairing_bound_infinite_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:17.30914+00:00
-- url     : https://prove2.me/submissions/35e243ca-1c49-479f-9209-3e1412ab7c7d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PairingBoundInfinitePlaces
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PairingBoundInfinitePlacesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_pairI_of_detMono


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
theorem _root_.solution : DetMono → PairI := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono | exact GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono | (intros; apply GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono <;> assumption)
end _root_.GlobalTheory.T
