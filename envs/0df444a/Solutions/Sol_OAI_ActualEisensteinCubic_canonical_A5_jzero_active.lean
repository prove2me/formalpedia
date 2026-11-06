-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jzero_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:34.758171+00:00
-- url     : https://prove2.me/submissions/fb8c613f-efa7-4213-8ef9-23794892ad4b

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_active_zero_local_row
import Theorems.Thm_OAI_ShortDraftLocal_trivial_fourier_coefficient
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open AddChar MulChar
open AddChar MulChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ2 : χ ^ 2 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (2:ℕ) ≠ 0) (by decide : (2:ℕ) < 6)
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
        (∑ h : (O ⧸ P)ˣ,
          ((χ⁻¹) ^ 2) (h : O ⧸ P) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    have hh : (h : O ⧸ P) ≠ 0 := Units.ne_zero h
    rw [pow_zero, ShortDraftLocal.trivial_fourier_coefficient ψ hψ h,
      if_neg hh, map_mul]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.active_zero_local_row χ ψ hχ2 ε x]
  ring
end OAI.ActualEisensteinCubic
