-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.OddDeriv.hasProd_tailProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:33:37.281799+00:00
-- url     : https://prove2.me/submissions/65d28f64-95d8-45f6-9490-0096cbaaafd4

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
theorem _root_.solution (τ : ℍ) (v : ℂ) :
    HasProd (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ) * v) (tailProd τ v) := by
  have hs : Summable fun n : ℕ => ‖-(ModularForm.eta_q n (τ : ℂ) * v)‖ := by
    have h := ModularForm.summable_eta_q τ
    simp only [norm_neg, norm_mul] at h ⊢
    exact h.mul_right _
  have hm : Multipliable fun n : ℕ => 1 + -(ModularForm.eta_q n (τ : ℂ) * v) :=
    multipliable_one_add_of_summable hs
  simp only [← sub_eq_add_neg] at hm
  exact hm.hasProd
end GlobalTheory.ThetaWeberRoad.OddDeriv
