-- Prove2me | solution 1 for GlobalTheory.HermFrame.del_finsetProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:09.293539+00:00
-- url     : https://prove2.me/submissions/94c1897f-9b1a-44dd-a93a-8d22f1451e07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernOneEqNegDdcLogDet
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
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
namespace GlobalTheory.HermFrame
theorem _root_.solution {ι : Type*} [DecidableEq ι] (t : Finset ι) {f : ι → E → ℂ} {z : E}
    (h : ∀ i ∈ t, DifferentiableAt ℝ (f i) z) (ξ : E) :
    del (fun x => ∏ i ∈ t, f i x) z ξ = ∑ i ∈ t, (∏ j ∈ t.erase i, f j z) * del (f i) z ξ := by
  have h1 := (HasFDerivAt.finsetProd (u := t) (g := f) (fun i hi => (h i hi).hasFDerivAt)).fderiv
  simp only [del_apply, h1, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.HermFrame
