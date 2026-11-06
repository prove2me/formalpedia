-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jfour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:34.163963+00:00
-- url     : https://prove2.me/submissions/7ce36688-e1ca-4553-ade2-5ca8a5cc37b3

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_six
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_nontrivial_fourier_coefficient
import Theorems.Thm_OAI_ShortDraftLocal_sextic_fourth_mask
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
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ4 : χ ^ 4 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) * gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (∑ h : (O ⧸ P)ˣ,
          (((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [ShortDraftLocal.nontrivial_fourier_coefficient (χ ^ 4) ψ hχ4 h,
      map_mul]
    simp only [inv_pow, MulChar.mul_apply]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.sextic_fourth_mask χ ψ hχ6 hψ (ε * x)]
  ring
end OAI.ActualEisensteinCubic
