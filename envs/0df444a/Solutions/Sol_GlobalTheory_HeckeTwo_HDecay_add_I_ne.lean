-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.add_I_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:35.036236+00:00
-- url     : https://prove2.me/submissions/d6da3152-134e-420b-9e36-66e6d84b95d3

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
theorem _root_.solution (hy : y ≠ 0) (t : ℝ) : (t : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this
end GlobalTheory.HeckeTwo.HDecay
