-- Prove2me | solution 1 for GlobalTheory.T.integralGLSet_isOpen_and_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:24:32.2546+00:00
-- url     : https://prove2.me/submissions/5df44628-0a72-42b3-9b35-58f1c3aeeeed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralGLSetIsOpenAndIsCompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralGLSetIsOpenAndIsCompactStatement
import Theorems.Thm_GlobalTheory_JR_GLift_glO_isOpen_isCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  first | exact @GlobalTheory.JR.GLift.glO_isOpen_isCompact | exact GlobalTheory.JR.GLift.glO_isOpen_isCompact | (intros; apply GlobalTheory.JR.GLift.glO_isOpen_isCompact <;> assumption)
end _root_.GlobalTheory.T
