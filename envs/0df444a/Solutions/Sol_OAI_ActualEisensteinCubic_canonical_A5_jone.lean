-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:28.643225+00:00
-- url     : https://prove2.me/submissions/80163327-d3e7-4109-b278-100dd8b14e87

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_six
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_sextic_fourier_theta_row
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
    (ψ : AddChar (O ⧸ P) ℂ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.sextic_fourier_theta_row
    (canonicalSextic P hgood) ψ (canonicalSextic_pow_six P hgood)
    (canonicalSextic_pow_ne_one P hgood hchar (by decide : (3:ℕ) ≠ 0)
      (by decide : (3:ℕ) < 6)) σ ε x
end OAI.ActualEisensteinCubic
