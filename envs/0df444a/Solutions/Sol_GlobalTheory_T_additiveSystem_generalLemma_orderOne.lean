-- Prove2me | solution 1 for GlobalTheory.T.additiveSystem_generalLemma_orderOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:22:39.068729+00:00
-- url     : https://prove2.me/submissions/fd30e884-aee8-4d26-bce2-efa094d94ed6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaOrderOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaOrderOneStatement
import Theorems.Thm_GlobalTheory_PMonE_gl1


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
theorem _root_.solution : GLOnto 1 ∧ GLCount 1 := by
  first | exact @GlobalTheory.PMonE.gl1 | exact GlobalTheory.PMonE.gl1 | (intros; apply GlobalTheory.PMonE.gl1 <;> assumption)
end _root_.GlobalTheory.T
