-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.sub_I_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:29.333679+00:00
-- url     : https://prove2.me/submissions/b5fb9be5-6219-4e22-bbe4-c83bbd8e1489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (t : ℝ) : (t : ℂ) - (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this
end GlobalTheory.HeckeTwo.HDecay
