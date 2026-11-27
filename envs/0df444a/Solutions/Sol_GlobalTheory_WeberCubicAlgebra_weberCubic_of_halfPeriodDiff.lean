-- Prove2me | solution 1 for GlobalTheory.WeberCubicAlgebra.weberCubic_of_halfPeriodDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:42:50.498973+00:00
-- url     : https://prove2.me/submissions/74822cf7-5f73-49cd-bc29-6201806365c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionsRootsOfCubicOfHalfPeriodDiff
import Theorems.Thm_GlobalTheory_WeberCubicAlgebra_half_root
import Theorems.Thm_GlobalTheory_WeberCubicAlgebra_roots_alg
import Theorems.Thm_GlobalTheory_WeberCubicAlgebra_coeffs
import Theorems.Thm_GlobalTheory_WeberCubicAlgebra_cubic_eq
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ThetaConstantWeber_disc_ne_zero
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ThetaConstantWeber_halfPeriods_notMem
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ThetaConstantWeber_jLat_eq
import Theorems.Thm_GlobalTheory_mem_lattice_periodPairOfTau


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Polynomial
open UpperHalfPlane hiding I
noncomputable section
open GlobalTheory GlobalTheory.WeberCubicAlgebra
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
namespace GlobalTheory.WeberCubicAlgebra
theorem _root_.solution : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ →
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.WeberCubic τ := by
  intro τ hd hj hw
  obtain ⟨d1, d2, d3⟩ := hd
  obtain ⟨w0, w1, w2⟩ := hw
  unfold JacobiProduct at hj
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : thetaConst 0 0 τ * thetaConst 0 1 τ * thetaConst 1 0 τ ≠ 0 := by
    rw [hj]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hη)
  have t0 : thetaConst 0 0 τ ≠ 0 := fun h => hprod (by simp [h])
  have t1 : thetaConst 0 1 τ ≠ 0 := fun h => hprod (by simp [h])
  have t2 : thetaConst 1 0 τ ≠ 0 := fun h => hprod (by simp [h])
  obtain ⟨n1, n2, n3⟩ := halfPeriods_notMem τ
  have mem : ∀ p q : ℤ, ((p : ℂ) * (τ : ℂ) + q) ∈ (GlobalTheory.periodPairOfTau τ).lattice := fun p q => by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    exact ⟨p, q, by ring⟩
  have r1 := half_root (GlobalTheory.periodPairOfTau τ) (t := 1 / 2) (by simpa using mem 0 1) n1
  have r2 := half_root (GlobalTheory.periodPairOfTau τ) (t := (τ : ℂ) / 2) (by
    have := mem 1 0
    convert this using 1
    push_cast
    ring) n2
  have r3 := half_root (GlobalTheory.periodPairOfTau τ) (t := (1 + (τ : ℂ)) / 2) (by
    have := mem 1 1
    convert this using 1
    push_cast
    ring) n3
  have hP : ((Real.pi : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ hp
  have h12 : wp τ (1 / 2) ≠ wp τ ((τ : ℂ) / 2) := by
    rw [← sub_ne_zero, d1]
    exact mul_ne_zero hP (pow_ne_zero _ t0)
  have h13 : wp τ (1 / 2) ≠ wp τ ((1 + (τ : ℂ)) / 2) := by
    rw [← sub_ne_zero, d2]
    exact mul_ne_zero hP (pow_ne_zero _ t1)
  have h23 : wp τ ((τ : ℂ) / 2) ≠ wp τ ((1 + (τ : ℂ)) / 2) := by
    intro h
    have h' : wp τ ((1 + (τ : ℂ)) / 2) - wp τ ((τ : ℂ) / 2) = 0 := by rw [h]; ring
    rw [d3] at h'
    exact mul_ne_zero hP (pow_ne_zero _ t2) h'
  have hw1 : wp τ (1 / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP (1 / 2) := rfl
  have hw2 : wp τ ((τ : ℂ) / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP ((τ : ℂ) / 2) := rfl
  have hw3 : wp τ ((1 + (τ : ℂ)) / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP ((1 + (τ : ℂ)) / 2) := rfl
  rw [← hw1] at r1
  rw [← hw2] at r2
  rw [← hw3] at r3
  obtain ⟨hg, hdisc⟩ := roots_alg h12 h13 h23 r1 r2 r3 d1 d2 d3
  have hjl : jLat τ * ((GlobalTheory.periodPairOfTau τ).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ).g₃ ^ 2) =
      1728 * (GlobalTheory.periodPairOfTau τ).g₂ ^ 3 := by
    rw [jLat_eq, div_mul_cancel₀ _ (disc_ne_zero τ)]
  rw [hdisc, hg] at hjl
  have hs : thetaConst 0 0 τ ^ 4 = thetaConst 0 1 τ ^ 4 + thetaConst 1 0 τ ^ 4 := by
    apply mul_left_cancel₀ hP
    linear_combination -d1 + d2 + d3
  have hJ4 : thetaConst 0 0 τ ^ 4 * thetaConst 0 1 τ ^ 4 * thetaConst 1 0 τ ^ 4 =
      16 * ModularForm.eta (τ : ℂ) ^ 12 := by
    have := congrArg (· ^ 4) hj
    linear_combination this
  have a0 : (thetaConst 0 0 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF τ ^ 24 := by
    rw [w0]; ring
  have a1 : (thetaConst 0 1 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF₁ τ ^ 24 := by
    rw [w1]; ring
  have a2 : (thetaConst 1 0 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF₂ τ ^ 24 := by
    rw [w2]; ring
  have A0 := pow_ne_zero 4 t0
  have B0 := pow_ne_zero 4 t1
  have D0 := pow_ne_zero 4 t2
  apply cubic_eq
  apply coeffs _ _ _ _ _ _ _ A0 B0 D0 hs
  · apply mul_left_cancel₀ A0
    linear_combination weberF τ ^ 24 * hJ4 - 16 * a0
  · apply mul_left_cancel₀ B0
    linear_combination weberF₁ τ ^ 24 * hJ4 - 16 * a1
  · apply mul_left_cancel₀ D0
    linear_combination weberF₂ τ ^ 24 * hJ4 - 16 * a2
  · have h16 : (16 : ℂ) * ((Real.pi : ℂ) ^ 2) ^ 6 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hP)
    apply mul_left_cancel₀ h16
    linear_combination hjl
end GlobalTheory.WeberCubicAlgebra
