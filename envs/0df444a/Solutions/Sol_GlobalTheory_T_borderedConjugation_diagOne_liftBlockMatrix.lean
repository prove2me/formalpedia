-- Prove2me | solution 1 for GlobalTheory.T.borderedConjugation_diagOne_liftBlockMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:18.619181+00:00
-- url     : https://prove2.me/submissions/53aa5ab5-1827-44b2-a27d-c225129a4d38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedConjugationDiagOneLiftBlockMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedConjugationDiagOneLiftBlockMatrixStatement
import Theorems.Thm_GlobalTheory_JR_Step_ActEmbLift_act_emb_lift


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
theorem _root_.solution : ∀ (k : Type) [CommRing k] (r : ℕ) (g : GL (Fin r) k) (Z : Gl r k) (μ l : k), act (GlobalTheory.JR.Step.emb r k g) (GlobalTheory.JR.Step.lift Z μ l) = GlobalTheory.JR.Step.lift (act g Z) μ l := by
  first | exact @GlobalTheory.JR.Step.ActEmbLift.act_emb_lift | exact GlobalTheory.JR.Step.ActEmbLift.act_emb_lift | (intros; apply GlobalTheory.JR.Step.ActEmbLift.act_emb_lift <;> assumption)
end _root_.GlobalTheory.T
