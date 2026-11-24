-- Prove2me | solution 1 for GlobalTheory.RealWeil.weightOp_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:07:14.941369+00:00
-- url     : https://prove2.me/submissions/5af04d07-ce52-4ff6-b34a-3985bec37015

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_weightOp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (k : ℕ) (f : Sch l) (x : EuclideanSpace ℝ l) :
    (weightOp l ^ k) f x = (((1 + ‖x‖ ^ 2) ^ k : ℝ) : ℂ) * f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, weightOp_apply, ih]
    push_cast
    ring
end GlobalTheory.RealWeil
