-- Prove2me | solution 1 for GlobalTheory.T.multiplicativity_finite_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:24:01.181623+00:00
-- url     : https://prove2.me/submissions/2fca3f99-d046-466e-bd50-6cc6d955af2f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlacesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_mulF


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
theorem _root_.solution : MulF := by
  first | exact @GlobalTheory.CompanionTheory.WedgeMinor.mulF | exact GlobalTheory.CompanionTheory.WedgeMinor.mulF | (intros; apply GlobalTheory.CompanionTheory.WedgeMinor.mulF <;> assumption)
end _root_.GlobalTheory.T
