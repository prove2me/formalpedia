-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.halfPeriodDiff_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:45:43.231556+00:00
-- url     : https://prove2.me/submissions/2f405072-1276-4bcd-9e9c-c2cb3bec896c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HalfPeriodDiffThetaFourthOfSigmaStarAddition
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_oddTheta_half
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_oddTheta_tau_half
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_oddTheta_one_add_tau_half
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_oddTheta_one_sub_tau_half
import Theorems.Thm_P2M_GlobalTheory_ThetaWeberRoad_oddTheta_one_add_tau_half__45cd36bb83c6
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_oddTheta_neg_tau_half
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_oddTheta_half_add_tau
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_oddTheta_addition
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ThetaConstantWeber_halfPeriods_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex
open scoped Real
noncomputable section
namespace GlobalTheory.ThetaWeberRoad
private theorem d_eq_sq_mul_pow_four_of_relations (p A B C g c e d1 d2 d3 : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hc : c ≠ 0) (hg : g ^ 2 = p ^ 2 * (A * B * C) ^ 2) (hc4 : c ^ 4 = e)
    (e1 : g ^ 2 * (-c * A * (-c * A)) = -((-C) ^ 2 * (-I * c * B) ^ 2 * d1))
    (e2 : g ^ 2 * (I * c * B * (I * c * B)) = -((-C) ^ 2 * (-c * A) ^ 2 * d2))
    (e3 : g ^ 2 * (-(e * C) * -C) = -((-c * A) ^ 2 * (-I * c * B) ^ 2 * d3)) :
    d1 = p ^ 2 * A ^ 4 ∧ d2 = p ^ 2 * B ^ 4 ∧ d3 = p ^ 2 * C ^ 4 := by
  rw [hg] at e1 e2 e3
  rw [← hc4] at e3
  have hI2 : I ^ 2 = -1 := Complex.I_sq
  refine ⟨?_, ?_, ?_⟩
  · have h : (c ^ 2 * B ^ 2 * C ^ 2) * d1 = (c ^ 2 * B ^ 2 * C ^ 2) * (p ^ 2 * A ^ 4) := by
      linear_combination (-1 : ℂ) * e1 + C ^ 2 * c ^ 2 * B ^ 2 * d1 * hI2
    exact mul_left_cancel₀ (by simp [hc, hB, hC]) h
  · have h : (c ^ 2 * A ^ 2 * C ^ 2) * d2 = (c ^ 2 * A ^ 2 * C ^ 2) * (p ^ 2 * B ^ 4) := by
      linear_combination e2 - p ^ 2 * A ^ 2 * B ^ 4 * C ^ 2 * c ^ 2 * hI2
    exact mul_left_cancel₀ (by simp [hc, hA, hC]) h
  · have h : (c ^ 4 * A ^ 2 * B ^ 2) * d3 = (c ^ 4 * A ^ 2 * B ^ 2) * (p ^ 2 * C ^ 4) := by
      linear_combination (-1 : ℂ) * e3 + c ^ 4 * A ^ 2 * B ^ 2 * d3 * hI2
    exact mul_left_cancel₀ (by simp [hc, hA, hB]) h
end GlobalTheory.ThetaWeberRoad
end
end

set_option autoImplicit false
open Complex
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad
namespace GlobalTheory.ThetaWeberRoad
theorem _root_.solution : Formalism.L2.Th1.F.SgStarAdd →
    (∀ (τ : UpperHalfPlane) (z : ℂ), Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) *
      GlobalTheory.ThetaWeberRoad.oddTheta τ z =
        deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z) →
    (∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ)
      (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0) →
    (∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ) →
    ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ := by
  intro hSA hI hD hJ τ
  obtain ⟨n1, n2, n3⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.halfPeriods_notMem τ
  have hd : deriv (oddTheta τ) 0 = -2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3 := (hD τ).deriv
  have hJ' : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ *
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ = 2 * ModularForm.eta (τ : ℂ) ^ 3 := hJ τ
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hABC : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ *
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := by
    rw [hJ']
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hη)
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ ≠ 0 := fun h => hABC (by rw [h]; ring)
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ ≠ 0 := fun h => hABC (by rw [h]; ring)
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := fun h => hABC (by rw [h]; ring)
  have hg : deriv (oddTheta τ) 0 ^ 2 = (π : ℂ) ^ 2 * (GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ *
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ) ^ 2 := by
    rw [hd, hJ']
    ring
  have hc4 : cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) ^ 4 = cexp (-((π : ℂ) * I * (τ : ℂ))) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e1 := oddTheta_addition hSA τ (hI τ) (1 / 2) ((τ : ℂ) / 2) n1 n2
  have e2 := oddTheta_addition hSA τ (hI τ) (1 / 2) ((1 + (τ : ℂ)) / 2) n1 n3
  have e3 := oddTheta_addition hSA τ (hI τ) ((1 + (τ : ℂ)) / 2) ((τ : ℂ) / 2) n3 n2
  rw [show (1 : ℂ) / 2 + (τ : ℂ) / 2 = (1 + (τ : ℂ)) / 2 by ring] at e1
  rw [show (1 : ℂ) / 2 + (1 + (τ : ℂ)) / 2 = 1 + (τ : ℂ) / 2 by ring,
    show (1 : ℂ) / 2 - (1 + (τ : ℂ)) / 2 = -((τ : ℂ) / 2) by ring] at e2
  rw [show (1 + (τ : ℂ)) / 2 + (τ : ℂ) / 2 = 1 / 2 + (τ : ℂ) by ring,
    show (1 + (τ : ℂ)) / 2 - (τ : ℂ) / 2 = 1 / 2 by ring] at e3
  rw [oddTheta_one_add_tau_half, oddTheta_one_sub_tau_half, oddTheta_half, oddTheta_tau_half] at e1
  rw [oddTheta_one_add_tau_half', oddTheta_neg_tau_half, oddTheta_half, oddTheta_one_add_tau_half] at e2
  rw [oddTheta_half_add_tau, oddTheta_half, oddTheta_one_add_tau_half, oddTheta_tau_half] at e3
  exact d_eq_sq_mul_pow_four_of_relations _ _ _ _ _ _ _ _ _ _ hA hB hC (Complex.exp_ne_zero _) hg hc4 e1 e2 e3
end GlobalTheory.ThetaWeberRoad
