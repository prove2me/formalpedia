-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.OddDeriv.tpFactor_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:17.108961+00:00
-- url     : https://prove2.me/submissions/9af5b84e-4d1b-42e8-b6cc-4e5b9bf5b371

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
theorem _root_.solution (τ : ℍ) (z : ℂ) (n : ℕ) :
    tpFactor τ (z + ((τ : ℂ) + 1) / 2) n =
      (1 - ModularForm.eta_q n (τ : ℂ) * 1) *
        (1 - ModularForm.eta_q n (τ : ℂ) * cexp (2 * π * I * z)) *
        (1 - cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) := by
  have hm : cexp (-(π * I)) = -1 := by rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hp : cexp (π * I) = -1 := Complex.exp_pi_mul_I
  have h1 : cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) + 2 * π * I * (z + ((τ : ℂ) + 1) / 2)) =
      -(cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z)) := by
    rw [show -(cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z)) =
      cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z) * cexp (π * I) by
        rw [hp]; ring, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  have h2 : cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) - 2 * π * I * (z + ((τ : ℂ) + 1) / 2)) =
      -(cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) := by
    rw [show -(cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) =
      cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z)) * cexp (-(π * I)) by
        rw [hm]; ring, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  unfold tpFactor
  rw [ModularForm.eta_q_eq_cexp, h1, h2]
  ring
end GlobalTheory.ThetaWeberRoad.OddDeriv
