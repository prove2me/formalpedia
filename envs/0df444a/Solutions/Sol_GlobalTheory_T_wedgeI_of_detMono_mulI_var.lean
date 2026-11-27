-- Prove2me | solution 1 for GlobalTheory.T.wedgeI_of_detMono_mulI_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:47.163141+00:00
-- url     : https://prove2.me/submissions/42e4f75a-5e56-48c3-8207-04f897f9f0a4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlaces
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundInfinitePlacesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_wedgeI_of_detMono_mulI


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
theorem _root_.solution : DetMono → MulI → WedgeI := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI | exact GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI | (intros; apply GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI <;> assumption)
end _root_.GlobalTheory.T
