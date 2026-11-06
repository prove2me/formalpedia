-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jfour_breveE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:10:46.771205+00:00
-- url     : https://prove2.me/submissions/f1f915b1-a75d-4659-bbc2-ba40bbd47b33

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jfour
import Theorems.Thm_OAI_PrimitiveTrace_eisTraceModChar_breveE_ne_one


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
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  exact canonical_A5_jfour (Ideal.span {p}) hgood hchar
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (eisTraceModChar_breveE_ne_one (Ideal.span {p}) p rfl hp) σ ε x
end OAI.ActualEisensteinCubic
