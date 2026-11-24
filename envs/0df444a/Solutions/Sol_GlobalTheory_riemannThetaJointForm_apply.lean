-- Prove2me | solution 1 for GlobalTheory.riemannThetaJointForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:40.629149+00:00
-- url     : https://prove2.me/submissions/f083b480-ee4f-4e46-a22d-d44c3ce387f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero



set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (a : ι → ℝ) (n : ι → ℤ)
    (p : (ι → ℂ) × (ι → ι → ℂ)) :
    riemannThetaJointForm a n p =
      2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (of p.2 *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
        (fun i => (n i : ℂ) + a i) ⬝ᵥ p.1) := by
  obtain ⟨w, A⟩ := p
  have : ∑ i, ∑ j, π * I * (((n i : ℂ) + a i) * ((n j : ℂ) + a j)) * A i j =
      π * I * ((fun i => (n i : ℂ) + a i) ⬝ᵥ (of A *ᵥ fun i => (n i : ℂ) + a i)) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [riemannThetaJointForm, ContinuousLinearMap.coprod_apply, riemannThetaForm_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, this]
  ring
end GlobalTheory
