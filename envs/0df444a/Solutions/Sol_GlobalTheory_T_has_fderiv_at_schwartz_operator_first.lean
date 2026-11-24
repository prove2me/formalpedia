-- Prove2me | solution 1 for GlobalTheory.T.has_fderiv_at_schwartz_operator_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:02:56.626992+00:00
-- url     : https://prove2.me/submissions/efa7ecc1-89b5-45d4-8b34-7532d77084fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFderivAtSchwartzOperatorFirst
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFderivAtSchwartzOperatorFirstStatement
import Theorems.Thm_GlobalTheory_SchwartzFstOp_hasFDerivAt_opFst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V'), HasFDerivAt (opFst T f) ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V') + (dSndCLM T f (y, x')).comp (ContinuousLinearMap.snd ℝ W V')) (y, x') := by
  first | exact @GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst | exact GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst | (intros; apply GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst <;> assumption)
end _root_.GlobalTheory.T
