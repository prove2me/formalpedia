-- Prove2me | solution 1 for GlobalTheory.RealWeil.fourierInv_besselOp_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:31.0326+00:00
-- url     : https://prove2.me/submissions/1692ad5d-56fc-47f1-a41d-60abd426347d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_fourierInv_besselOp

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
theorem _root_.solution (k : ℕ) (f : Sch l) : 𝓕⁻ ((besselOp l ^ k) f) = (weightOp l ^ k) (𝓕⁻ f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, fourierInv_besselOp, ih]
end GlobalTheory.RealWeil
