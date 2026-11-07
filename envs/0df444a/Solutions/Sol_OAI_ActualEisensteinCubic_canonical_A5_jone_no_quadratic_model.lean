-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jone_no_quadratic_model
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:38.524126+00:00
-- url     : https://prove2.me/submissions/499ba55d-b82c-4500-b8cc-75c93cb7ecee

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jone_direct
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jone_direct_not_quadratic
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jone_direct_scalar_ne_zero
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLocal_no_quadratic_scalar
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
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ActualEisensteinCubic
open MulChar AddChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ : (O ⧸ P)ˣ) (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    ¬ ∃ d : ℂ, ∀ x : O ⧸ P,
      (Nat.card (O ⧸ P) : ℂ)⁻¹ *
        (∑ h : (O ⧸ P)ˣ,
          (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
          (χ ^ 2) (σ * h) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
        d * (χ ^ 3) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := canonicalSextic P hgood
  let S : ℂ := (Nat.card (O ⧸ P) : ℂ)⁻¹ *
    gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε
  let c : ℂ := (χ ^ 2) σ * S
  have hχ : χ ≠ χ ^ 3 := canonical_A5_jone_direct_not_quadratic P hgood hchar
  have hS : S ≠ 0 := by
    simpa only [S, χ] using
      canonical_A5_jone_direct_scalar_ne_zero P hgood hchar ψ hψ ε hε
  have hσ : (χ ^ 2) (σ : O ⧸ P) ≠ 0 :=
    (χ ^ 2).apply_ne_zero_iff.mpr σ.isUnit
  have hc : c ≠ 0 := mul_ne_zero hσ hS
  dsimp
  intro hmodel
  apply ShortDraftLocal.no_quadratic_scalar χ hχ c hc
  obtain ⟨d, hd⟩ := hmodel
  refine ⟨d, ?_⟩
  intro x
  have hrow := canonical_A5_jone_direct P hgood hchar ψ σ ε x
  have hx := hd x
  dsimp only at hrow hx
  calc
    c * χ x =
      (Nat.card (O ⧸ P) : ℂ)⁻¹ *
        (∑ h : (O ⧸ P)ˣ,
          (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
          (χ ^ 2) (σ * h) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
            rw [hrow]
    _ = d * (χ ^ 3) x := hx
end OAI.ActualEisensteinCubic
