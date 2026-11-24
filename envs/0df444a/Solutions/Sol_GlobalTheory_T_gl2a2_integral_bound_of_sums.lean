-- Prove2me | solution 1 for GlobalTheory.T.gl2a2_integral_bound_of_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:29.329225+00:00
-- url     : https://prove2.me/submissions/2230f265-8e97-4ea9-aa51-98edbc908dd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2Integrality
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2IntegralityStatement
import Theorems.Thm_GlobalTheory_PsiTail_psi_tail_bound


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
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.PartialSumIntegralBound := by
  first | exact @GlobalTheory.PsiTail.psi_tail_bound | exact GlobalTheory.PsiTail.psi_tail_bound | (intros; apply GlobalTheory.PsiTail.psi_tail_bound <;> assumption)
end _root_.GlobalTheory.T
