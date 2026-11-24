-- Prove2me | solution 1 for GlobalTheory.SchwartzFstOp.dSndCLM_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:45.572917+00:00
-- url     : https://prove2.me/submissions/0ba84698-9912-4f50-b072-90130ea0f965

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open GlobalTheory GlobalTheory.SchwartzFstOp
variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.SchwartzFstOp
theorem _root_.solution [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (p : W × V')
    (v' : V') : dSndCLM T f p v' = opFst T (lineSnd v' f) p := rfl
end GlobalTheory.SchwartzFstOp
