-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.iteratedDeriv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:36:23.584875+00:00
-- url     : https://prove2.me/submissions/aa842330-5ce7-49ac-9fdd-925c53443012

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_wSpan_deriv

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
variable {σ y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (n : ℕ) : iteratedDeriv n (wF σ y 0 0) ∈ wSpan σ y := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    exact Submodule.subset_span ⟨(0, 0), rfl⟩
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (wSpan_deriv hy ih).2
end GlobalTheory.HeckeTwo.HDecay
