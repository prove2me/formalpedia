-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.OddDeriv.continuousAt_tailProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:36:08.884858+00:00
-- url     : https://prove2.me/submissions/b36734a6-9560-4e02-b11d-4ba61ed5ae91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv
namespace GlobalTheory.ThetaWeberRoad.OddDeriv
theorem _root_.solution (τ : ℍ) (v₀ : ℂ) : ContinuousAt (tailProd τ) v₀ := by
  have hK : IsCompact (Metric.closedBall v₀ 1) := isCompact_closedBall v₀ 1
  have hu : Summable fun n : ℕ => ‖ModularForm.eta_q n (τ : ℂ)‖ * (‖v₀‖ + 1) := by
    have h := ModularForm.summable_eta_q τ
    simp only [norm_neg] at h
    exact h.mul_right _
  have H := Summable.hasProdUniformlyOn_nat_one_add
    (f := fun n v => -(ModularForm.eta_q n (τ : ℂ) * v)) hK hu
    (Filter.Eventually.of_forall fun n v hv => by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_of_mem_closedBall hv) (norm_nonneg _))
    (fun n => by fun_prop)
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at H
  have hc := H.continuousOn (Frequently.of_forall fun s =>
    (continuous_finsetProd s fun i _ => by fun_prop).continuousOn)
  have : ContinuousOn (tailProd τ) (Metric.closedBall v₀ 1) := by
    refine hc.congr fun v _ => ?_
    simp [tailProd, sub_eq_add_neg]
  exact this.continuousAt (Metric.closedBall_mem_nhds v₀ one_pos)
end GlobalTheory.ThetaWeberRoad.OddDeriv
