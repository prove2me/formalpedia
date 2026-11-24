-- Prove2me | solution 1 for GlobalTheory.RealWeil.norm_weightOp_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:19.2813+00:00
-- url     : https://prove2.me/submissions/b5e2a801-0c8a-40b7-a29d-6a91712a52be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_weightOp_pow_apply

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
    ‖(weightOp l ^ k) f x‖ = (1 + ‖x‖ ^ 2) ^ k * ‖f x‖ := by
  rw [weightOp_pow_apply, norm_mul, norm_real, Real.norm_of_nonneg (by positivity)]
end GlobalTheory.RealWeil
