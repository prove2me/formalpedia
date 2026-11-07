-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jzero_direct_active
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:49:59.417649+00:00
-- url     : https://prove2.me/submissions/231c94fd-31e5-4328-8411-30f45f7c9925

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_direct_theta_active_zero_fourier_row
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (-(Nat.card (O ⧸ P) : ℂ)⁻¹) *
      (∑ h : (O ⧸ P)ˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(χ ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hχ₂ : (canonicalSextic P hgood) ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.direct_theta_active_zero_fourier_row
    (canonicalSextic P hgood) ψ hχ₂ σ ε x
end OAI.ActualEisensteinCubic
