-- Prove2me | solution 1 for GlobalTheory.T.wedge_subspace_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:51.278719+00:00
-- url     : https://prove2.me/submissions/074d5ec6-5708-4546-a50e-c92aeea6e33a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeSubspaceBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeSubspaceBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeNorm_wedgeSub


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
theorem _root_.solution : WedgeSub := by
  first | exact @GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub | exact GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub | (intros; apply GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub <;> assumption)
end _root_.GlobalTheory.T
