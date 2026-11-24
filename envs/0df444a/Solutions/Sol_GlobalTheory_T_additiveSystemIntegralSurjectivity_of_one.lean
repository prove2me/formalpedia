-- Prove2me | solution 1 for GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:02:40.683821+00:00
-- url     : https://prove2.me/submissions/3f34cc8b-1060-4178-a90f-6bbc0222aef3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemIntegralSurjectivityOfOneStatement
import Theorems.Thm_GlobalTheory_PMonE_glOnto_of_one


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
theorem _root_.solution : ∀ N : ℕ, 1 ≤ N → GLOnto 1 → GLOnto N := by
  first | exact @GlobalTheory.PMonE.glOnto_of_one | exact GlobalTheory.PMonE.glOnto_of_one | (intros; apply GlobalTheory.PMonE.glOnto_of_one <;> assumption)
end _root_.GlobalTheory.T
