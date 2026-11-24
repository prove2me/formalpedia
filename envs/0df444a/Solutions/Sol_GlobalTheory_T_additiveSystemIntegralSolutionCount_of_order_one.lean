-- Prove2me | solution 1 for GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:02:27.270895+00:00
-- url     : https://prove2.me/submissions/60892223-584e-4478-84aa-f72a3eb19fc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSolutionCountOfOrderOneStatement
import Theorems.Thm_GlobalTheory_PMonE_LinCount_glCount_of_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ N : ℕ, 1 ≤ N → GLCount 1 → GLCount N := by
  first | exact @GlobalTheory.PMonE.LinCount.glCount_of_one | exact GlobalTheory.PMonE.LinCount.glCount_of_one | (intros; apply GlobalTheory.PMonE.LinCount.glCount_of_one <;> assumption)
end _root_.GlobalTheory.T
