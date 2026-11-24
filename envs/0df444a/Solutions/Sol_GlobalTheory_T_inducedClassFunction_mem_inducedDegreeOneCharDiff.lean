-- Prove2me | solution 1 for GlobalTheory.T.inducedClassFunction_mem_inducedDegreeOneCharDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:14:53.221536+00:00
-- url     : https://prove2.me/submissions/e17acfbd-45bf-44e1-ad8d-43c287a10ba8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionMemInducedDegreeOneCharDiff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionMemInducedDegreeOneCharDiffStatement
import Theorems.Thm_GlobalTheory_BrauerZero_ind_mem_D0_of_mem_D0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ), f ∈ D0 E → ind E f ∈ D0 G := by
  first | exact @GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 | exact GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 | (intros; apply GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 <;> assumption)
end _root_.GlobalTheory.T
