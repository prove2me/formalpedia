-- Prove2me | solution 1 for GlobalTheory.SchwartzFstOp.exists_tensorId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:41:28.611067+00:00
-- url     : https://prove2.me/submissions/edee052a-d514-4896-b3fa-e3310e1e0f42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasFderivAtSchwartzOperatorFirstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzOperatorParametricExtension
import Theorems.Thm_GlobalTheory_SchwartzFstOp_tensorId_apply

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
theorem _root_.solution : ∀ {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [NormedAddCommGroup V']
    [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ),
    ∃ P : SchwartzMap (V × V') ℂ →L[ℂ] SchwartzMap (W × V') ℂ, ∀ (f : SchwartzMap (V × V') ℂ) (x' : V')
      (h : SchwartzMap V ℂ), (∀ x, h x = f (x, x')) → ∀ y, P f (y, x') = T h y := by
  intro V W V' _ _ _ _ _ _ _ _ _ T
  refine ⟨tensorId T, fun f x' h hh y => ?_⟩
  have e : sliceCLM x' f = h := by
    ext x
    rw [sliceCLM_apply, hh]
  rw [tensorId_apply, e]
end GlobalTheory.SchwartzFstOp
