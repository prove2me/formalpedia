-- Prove2me | solution 1 for GlobalTheory.HermFrame.del_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:27.458685+00:00
-- url     : https://prove2.me/submissions/18904a30-744a-44dd-a370-2cdabc792a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
import Theorems.Thm_GlobalTheory_HermFrame_del_finsetProd
import Theorems.Thm_GlobalTheory_HermFrame_trace_adjugate_mul_eq_sum
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_del_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m n l : Type*}
variable [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ} {z : E}
namespace GlobalTheory.HermFrame
theorem _root_.solution (h : MContDiffAt 1 H z) (ξ : E) :
    del (fun x => (H x).det) z ξ = ((H z).adjugate * mdel H z ξ).trace := by
  have hp : ∀ σ : Equiv.Perm n, DifferentiableAt ℝ (fun x => ∏ i, H x (σ i) i) z := fun σ =>
    (contDiffAt_prod fun c _ => h (σ c) c).differentiableAt one_ne_zero
  simp only [det_apply']
  rw [del_sum fun σ _ => (differentiableAt_const _).fun_mul (hp σ), trace_adjugate_mul_eq_sum,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [del_mul (differentiableAt_const _) (hp σ),
    del_finsetProd _ (f := fun i x => H x (σ i) i) fun i _ => h.diff _ _]
  simp
end GlobalTheory.HermFrame
