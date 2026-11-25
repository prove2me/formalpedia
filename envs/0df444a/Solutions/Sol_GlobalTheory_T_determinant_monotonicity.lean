-- Prove2me | solution 1 for GlobalTheory.T.determinant_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:37.581798+00:00
-- url     : https://prove2.me/submissions/196c762a-bb67-43f2-b488-1f385ffaf03d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DeterminantMonotonicity
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DeterminantMonotonicityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_DetMonotone_detMono


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
theorem _root_.solution : DetMono := by
  first | exact @GlobalTheory.CompanionTheory.DetMonotone.detMono | exact GlobalTheory.CompanionTheory.DetMonotone.detMono | (intros; apply GlobalTheory.CompanionTheory.DetMonotone.detMono <;> assumption)
end _root_.GlobalTheory.T
