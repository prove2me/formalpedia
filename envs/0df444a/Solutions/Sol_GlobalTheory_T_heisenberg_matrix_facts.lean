-- Prove2me | solution 1 for GlobalTheory.T.heisenberg_matrix_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:09:22.630099+00:00
-- url     : https://prove2.me/submissions/4f56be05-5385-4716-880f-c04916761285

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFactsStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertHeis_Heisenberg__9b2968164a68


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Heis := by
  first | exact @GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ | exact GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ | (intros; apply GlobalTheory.CompanionTheory.InertHeis.Heisenberg₂ <;> assumption)
end _root_.GlobalTheory.T
