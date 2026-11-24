-- Prove2me | solution 1 for GlobalTheory.RealWeil.weightOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:50:12.817091+00:00
-- url     : https://prove2.me/submissions/7ba7a349-0383-4617-ae03-7c724b5c2455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inr


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
theorem _root_.solution (f : Sch l) (x : EuclideanSpace ℝ l) :
    weightOp l f x = ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) * f x := by
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [weightOp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, SchwartzMap.sub_apply, SchwartzMap.smul_apply,
    SchwartzMap.sum_apply, dRho_single_inr, smul_eq_mul, EuclideanSpace.real_norm_sq_eq]
  push_cast
  rw [add_mul, one_mul, Finset.mul_sum, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp
  rw [I_sq]
  ring
end GlobalTheory.RealWeil
