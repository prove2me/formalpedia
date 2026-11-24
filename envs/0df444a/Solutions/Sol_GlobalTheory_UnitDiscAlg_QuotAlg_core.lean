-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.QuotAlg.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:27.230883+00:00
-- url     : https://prove2.me/submissions/625c4236-760b-479d-9eae-01f73455c93b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitAndIntegInvOfNormDetEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnit
import Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_eq_of_comp
import Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_cm_mul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_comp1
import Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_comp2
import Theorems.Thm_GlobalTheory_UnitDiscAlg_QuotAlg_comp3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.QuotAlg
variable {R : Type*} [CommRing R]
namespace GlobalTheory.UnitDiscAlg.QuotAlg
theorem _root_.solution (p pi c ci u a₂ a₃ b e₁ e₂ e₃ k11 k12 k13 k21 k22 k23 k31 k32 k33 k41 k42 k43 : R)
    (hp : p * pi = 1) (hci : c * ci = 1)
    (h11 : e₁ * e₁ = e₁) (h22 : e₂ * e₂ = e₂) (h33 : e₃ * e₃ = e₃)
    (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (hs : e₁ + e₂ + e₃ = 1)
    (hc1 : c * e₁ = u * e₁) (hc2 : c * e₂ = p * (a₂ * e₂)) (hc3 : ci * e₃ = p * (a₃ * e₃))
    (hk11 : (p + u ^ 2) * k11 = 1) (hk12 : (1 + p * a₂ ^ 2) * k12 = 1)
    (hk13 : (1 + p ^ 3 * a₃ ^ 2) * k13 = 1)
    (hk21 : (p + u ^ 3) * k21 = 1) (hk22 : (1 + p ^ 2 * a₂ ^ 3) * k22 = 1)
    (hk23 : (1 + p ^ 4 * a₃ ^ 3) * k23 = 1)
    (hk31 : (p * u ^ 2 + b ^ 2) * k31 = 1) (hk32 : (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 = 1)
    (hk33 : (1 + p * b ^ 2 * a₃ ^ 2) * k33 = 1)
    (hk41 : (p * u ^ 3 + b ^ 3) * k41 = 1) (hk42 : (b ^ 3 + p ^ 4 * a₂ ^ 3) * k42 = 1)
    (hk43 : (1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * k43 = 1) :
    (p + c ^ 2) * (k11 * e₁ + (pi * k12) * e₂ + (ci ^ 2 * k13) * e₃) = 1 ∧
    (p + c ^ 3) * (k21 * e₁ + (pi * k22) * e₂ + (ci ^ 3 * k23) * e₃) = 1 ∧
    (p * c ^ 2 + b ^ 2) * (k31 * e₁ + k32 * e₂ + (pi * ci ^ 2 * k33) * e₃) = 1 ∧
    (p * c ^ 3 + b ^ 3) * (k41 * e₁ + k42 * e₂ + (pi * ci ^ 3 * k43) * e₃) = 1 ∧
    (p * c ^ 3 + b ^ 3) * (p + c ^ 2) =
      (((p * u ^ 3 + b ^ 3) * (p + u ^ 2) * k21 * k31) * e₁
        + ((b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * k22 * k32) * e₂
        + ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * k23 * k33) * e₃)
        * ((p + c ^ 3) * (p * c ^ 2 + b ^ 2)) ∧
    (((p * u ^ 3 + b ^ 3) * (p + u ^ 2) * k21 * k31) * e₁
        + ((b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * k22 * k32) * e₂
        + ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * k23 * k33) * e₃) *
      (((p + u ^ 3) * (p * u ^ 2 + b ^ 2) * k41 * k11) * e₁
        + ((1 + p ^ 2 * a₂ ^ 3) * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k42 * k12) * e₂
        + ((1 + p ^ 4 * a₃ ^ 3) * (1 + p * b ^ 2 * a₃ ^ 2) * k43 * k13) * e₃) = 1 := by
  have hd3 : e₃ = p * c * a₃ * e₃ := by linear_combination c * hc3 - e₃ * hci

  have LargeParameterEstimates : (p + c ^ 2) * e₁ = ((p + u ^ 2) * 1) * e₁ := by linear_combination (c + u) * hc1
  have F12 : (p + c ^ 2) * e₂ = ((1 + p * a₂ ^ 2) * p) * e₂ := by
    linear_combination (c + p * a₂) * hc2
  have InertPlaceConditions : (p + c ^ 2) * e₃ = ((1 + p ^ 3 * a₃ ^ 2) * c ^ 2) * e₃ := by
    linear_combination p * (1 + p * c * a₃) * hd3
  have F21 : (p + c ^ 3) * e₁ = ((p + u ^ 3) * 1) * e₁ := by
    linear_combination (c ^ 2 + c * u + u ^ 2) * hc1
  have F22 : (p + c ^ 3) * e₂ = ((1 + p ^ 2 * a₂ ^ 3) * p) * e₂ := by
    linear_combination (c ^ 2 + c * p * a₂ + p ^ 2 * a₂ ^ 2) * hc2
  have F23 : (p + c ^ 3) * e₃ = ((1 + p ^ 4 * a₃ ^ 3) * c ^ 3) * e₃ := by
    linear_combination p * (1 + p * c * a₃ + (p * c * a₃) ^ 2) * hd3
  have F31 : (p * c ^ 2 + b ^ 2) * e₁ = ((p * u ^ 2 + b ^ 2) * 1) * e₁ := by
    linear_combination p * (c + u) * hc1
  have F32 : (p * c ^ 2 + b ^ 2) * e₂ = ((b ^ 2 + p ^ 3 * a₂ ^ 2) * 1) * e₂ := by
    linear_combination p * (c + p * a₂) * hc2
  have F33 : (p * c ^ 2 + b ^ 2) * e₃ = ((1 + p * b ^ 2 * a₃ ^ 2) * (p * c ^ 2)) * e₃ := by
    linear_combination b ^ 2 * (1 + p * c * a₃) * hd3
  have F41 : (p * c ^ 3 + b ^ 3) * e₁ = ((p * u ^ 3 + b ^ 3) * 1) * e₁ := by
    linear_combination p * (c ^ 2 + c * u + u ^ 2) * hc1
  have F42 : (p * c ^ 3 + b ^ 3) * e₂ = ((b ^ 3 + p ^ 4 * a₂ ^ 3) * 1) * e₂ := by
    linear_combination p * (c ^ 2 + c * p * a₂ + p ^ 2 * a₂ ^ 2) * hc2
  have F43 : (p * c ^ 3 + b ^ 3) * e₃ = ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (p * c ^ 3)) * e₃ := by
    linear_combination b ^ 3 * (1 + p * c * a₃ + (p * c * a₃) ^ 2) * hd3
  have c1 := comp1 h11 h12 h13
  have c2 := comp2 h12 h22 h23
  have c3 := comp3 h13 h23 h33
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul LargeParameterEstimates (c1 _ _ _)]; linear_combination e₁ * hk11
    · rw [cm_mul F12 (c2 _ _ _)]; linear_combination e₂ * p * pi * hk12 + e₂ * hp
    · rw [cm_mul InertPlaceConditions (c3 _ _ _)]
      linear_combination e₃ * (c * ci) ^ 2 * hk13 + e₃ * (c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F21 (c1 _ _ _)]; linear_combination e₁ * hk21
    · rw [cm_mul F22 (c2 _ _ _)]; linear_combination e₂ * p * pi * hk22 + e₂ * hp
    · rw [cm_mul F23 (c3 _ _ _)]
      linear_combination e₃ * (c * ci) ^ 3 * hk23 + e₃ * ((c * ci) ^ 2 + c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F31 (c1 _ _ _)]; linear_combination e₁ * hk31
    · rw [cm_mul F32 (c2 _ _ _)]; linear_combination e₂ * hk32
    · rw [cm_mul F33 (c3 _ _ _)]
      linear_combination e₃ * p * pi * (c * ci) ^ 2 * hk33 + e₃ * (c * ci) ^ 2 * hp
        + e₃ * (c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F41 (c1 _ _ _)]; linear_combination e₁ * hk41
    · rw [cm_mul F42 (c2 _ _ _)]; linear_combination e₂ * hk42
    · rw [cm_mul F43 (c3 _ _ _)]
      linear_combination e₃ * p * pi * (c * ci) ^ 3 * hk43 + e₃ * (c * ci) ^ 3 * hp
        + e₃ * ((c * ci) ^ 2 + c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F41 LargeParameterEstimates, cm_mul (c1 _ _ _) (cm_mul F21 F31)]
      linear_combination (-(p * u ^ 3 + b ^ 3) * (p + u ^ 2) * e₁) * ((p * u ^ 2 + b ^ 2) * k31 * hk21 + hk31)
    · rw [cm_mul F42 F12, cm_mul (c2 _ _ _) (cm_mul F22 F32)]
      linear_combination (-(b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * p * e₂) * ((b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 * hk22 + hk32)
    · rw [cm_mul F43 InertPlaceConditions, cm_mul (c3 _ _ _) (cm_mul F23 F33)]
      linear_combination (-(1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * p * c ^ 5 * e₃) * ((1 + p * b ^ 2 * a₃ ^ 2) * k33 * hk23 + hk33)
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul (c1 _ _ _) (c1 _ _ _)]
      linear_combination e₁ * ((p + u ^ 3) * k21 * (p * u ^ 2 + b ^ 2) * k31 * (p + u ^ 2) * k11 * hk41
        + (p + u ^ 3) * k21 * (p * u ^ 2 + b ^ 2) * k31 * hk11 + (p + u ^ 3) * k21 * hk31 + hk21)
    · rw [cm_mul (c2 _ _ _) (c2 _ _ _)]
      linear_combination e₂ * ((1 + p ^ 2 * a₂ ^ 3) * k22 * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 * (1 + p * a₂ ^ 2) * k12 * hk42
        + (1 + p ^ 2 * a₂ ^ 3) * k22 * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 * hk12 + (1 + p ^ 2 * a₂ ^ 3) * k22 * hk32 + hk22)
    · rw [cm_mul (c3 _ _ _) (c3 _ _ _)]
      linear_combination e₃ * ((1 + p ^ 4 * a₃ ^ 3) * k23 * (1 + p * b ^ 2 * a₃ ^ 2) * k33 * (1 + p ^ 3 * a₃ ^ 2) * k13 * hk43
        + (1 + p ^ 4 * a₃ ^ 3) * k23 * (1 + p * b ^ 2 * a₃ ^ 2) * k33 * hk13 + (1 + p ^ 4 * a₃ ^ 3) * k23 * hk33 + hk23)
end GlobalTheory.UnitDiscAlg.QuotAlg
