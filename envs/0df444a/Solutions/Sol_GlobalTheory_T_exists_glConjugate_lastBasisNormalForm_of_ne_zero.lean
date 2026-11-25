-- Prove2me | solution 1 for GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:15:15.073773+00:00
-- url     : https://prove2.me/submissions/1509ebe4-6d25-4f26-be79-58a4d6de2620

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlConjugateLastBasisNormalFormOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlConjugateLastBasisNormalFormOfNeZeroStatement
import Theorems.Thm_GlobalTheory_JR_Step_glNormal_of_ne_zero


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
theorem _root_.solution : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 → ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  first | exact @GlobalTheory.JR.Step.glNormal_of_ne_zero | exact GlobalTheory.JR.Step.glNormal_of_ne_zero | (intros; apply GlobalTheory.JR.Step.glNormal_of_ne_zero <;> assumption)
end _root_.GlobalTheory.T
