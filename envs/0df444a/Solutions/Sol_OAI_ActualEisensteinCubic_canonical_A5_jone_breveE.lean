-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jone_breveE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:10:46.157105+00:00
-- url     : https://prove2.me/submissions/c8512a2f-0724-4fce-9d2e-f5fa2a3c932a

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jone


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
open ConcreteTraceCRT PrimitiveTrace
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (p : O) (hp : p ≠ 0)
    [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (σ : (O ⧸ Ideal.span {p})ˣ) (ε x : O ⧸ Ideal.span {p}) :
    let P := Ideal.span {p}
    let χ := canonicalSextic P hgood
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by
  exact canonical_A5_jone (Ideal.span {p}) hgood hchar
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) σ ε x
end OAI.ActualEisensteinCubic
