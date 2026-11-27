-- Prove2me | solution 1 for GlobalTheory.T.wedge_bound_finite_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:49.246245+00:00
-- url     : https://prove2.me/submissions/f669180c-d38b-4f3a-97dc-83232b34f877

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlacesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_wedgeF_of_mulF


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
theorem _root_.solution : MulF → WedgeF := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF | exact GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF | (intros; apply GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF <;> assumption)
end _root_.GlobalTheory.T
