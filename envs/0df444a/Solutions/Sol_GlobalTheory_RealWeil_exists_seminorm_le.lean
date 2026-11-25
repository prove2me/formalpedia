-- Prove2me | solution 1 for GlobalTheory.RealWeil.exists_seminorm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:30:39.762471+00:00
-- url     : https://prove2.me/submissions/995f3f12-db93-4615-900b-c7808e33b64d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_iteratedLineDeriv_mem_weylAlg
import Theorems.Thm_GlobalTheory_RealWeil_weightOp_mem
import Theorems.Thm_GlobalTheory_RealWeil_norm_weightOp_pow_apply
import Theorems.Thm_GlobalTheory_RealWeil_exists_norm_apply_le
import Theorems.Thm_GlobalTheory_RealWeil_norm_multilinear_le

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
theorem _root_.solution (k n : ℕ) :
    ∃ A : (Fin n → l) → (Sch l →L[ℂ] Sch l), (∀ r, A r ∈ weylAlg l) ∧
      ∀ f : Sch l, SchwartzMap.seminorm ℂ k n f ≤ ∑ r, ‖(A r f).toLp 2 volume‖ := by
  obtain ⟨A, hA, h⟩ := exists_norm_apply_le (l := l)
  refine ⟨fun r => A * weightOp l ^ k * iteratedLineDerivOpCLM ℂ (Sch l) fun i => EuclideanSpace.single (r i) 1,
    fun r => mul_mem (mul_mem hA (pow_mem weightOp_mem _)) (iteratedLineDeriv_mem_weylAlg _), fun f => ?_⟩
  refine seminorm_le_bound ℂ k n f (by positivity) fun x => ?_
  refine (mul_le_mul_of_nonneg_left (norm_multilinear_le _) (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => le_trans ?_ (h _ x)
  refine le_trans ?_ (norm_weightOp_pow_apply k
    (iteratedLineDerivOpCLM ℂ (Sch l) (fun i => EuclideanSpace.single (r i) 1) f) x).ge
  rw [iteratedLineDerivOpCLM_apply, iteratedLineDerivOp_eq_iteratedFDeriv]
  gcongr
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
end GlobalTheory.RealWeil
