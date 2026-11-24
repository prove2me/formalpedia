-- Prove2me | solution 1 for GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:02:43.006409+00:00
-- url     : https://prove2.me/submissions/2e0f56cf-5114-48a1-a952-8120c17d3dba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemSurjectivityAndCountOrderZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemSurjectivityAndCountOrderZeroStatement
import Theorems.Thm_GlobalTheory_PMonE_glOnto_zero_and_glCount_zero


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
theorem _root_.solution : GLOnto 0 ∧ GLCount 0 := by
  first | exact @GlobalTheory.PMonE.glOnto_zero_and_glCount_zero | exact GlobalTheory.PMonE.glOnto_zero_and_glCount_zero | (intros; apply GlobalTheory.PMonE.glOnto_zero_and_glCount_zero <;> assumption)
end _root_.GlobalTheory.T
