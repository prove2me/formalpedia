-- Prove2me | solution 1 for GlobalTheory.SchwartzFstOp.tensorId_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:56.37046+00:00
-- url     : https://prove2.me/submissions/8e0655e7-5003-4b81-9dfa-e87be2738210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFderivAtSchwartzOperatorFirstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzOperatorParametricExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.SchwartzFstOp
variable {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [FiniteDimensional ℝ V']
namespace GlobalTheory.SchwartzFstOp
theorem _root_.solution (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, ℂ)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V') :
    tensorId T f (y, x') = T (sliceCLM x' f) y := rfl
end GlobalTheory.SchwartzFstOp
