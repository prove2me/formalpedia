-- Prove2me | solution 1 for GlobalTheory.RealWeil.norm_gau
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:09.199073+00:00
-- url     : https://prove2.me/submissions/5eabdbb9-3070-412b-9fbf-997e8f8ab7b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
namespace GlobalTheory.RealWeil
theorem _root_.solution (u : V) : ‖gau u‖ = Real.exp (-(π / 2) * ‖u‖ ^ 2) := by
  unfold gau
  rw [Complex.norm_exp]
  congr 1
  have : (-(π / 2 : ℂ) * (‖u‖ : ℂ) ^ 2) = ((-(π / 2) * ‖u‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ofReal_re]
end GlobalTheory.RealWeil
