-- Prove2me | solution 1 for GlobalTheory.T.pairing_bound_finite_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:09.98593+00:00
-- url     : https://prove2.me/submissions/2349c6c2-0e24-434a-b9a5-54f30e930e36

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PairingBoundFinitePlaces
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PairingBoundFinitePlacesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_pairF_of_mulF


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
theorem _root_.solution : MulF → PairF := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF | exact GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF | (intros; apply GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF <;> assumption)
end _root_.GlobalTheory.T
