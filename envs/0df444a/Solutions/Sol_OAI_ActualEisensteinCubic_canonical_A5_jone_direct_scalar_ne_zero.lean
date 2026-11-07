-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_A5_jone_direct_scalar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:45:48.34495+00:00
-- url     : https://prove2.me/submissions/6ad84c0c-ec56-41d7-9d60-0576f6bc23c8

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
open OAI.ActualEisensteinCubic
open AddChar MulChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) ≠ 0 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := canonicalSextic P hgood
  have hχ : χ ≠ 1 := by
    simpa only [χ, pow_one] using
      (canonicalSextic_pow_ne_one P hgood hchar
        (j := 1) (by decide) (by decide))
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  have hcard : (Fintype.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : O ⧸ P)⟩).ne'
  have hψshift : (ψ.mulShift (-1)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one
      (hψ (neg_ne_zero.mpr (one_ne_zero : (1 : O ⧸ P) ≠ 0)))
  have hg1 : gaussSum χ (ψ.mulShift (-1)) ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard hχ hψshift
  have hg2 : gaussSum χ⁻¹ ψ ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard hχinv hψ
  have hχε : χ ε ≠ 0 := χ.apply_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mpr hε)
  dsimp only
  rw [Nat.card_eq_fintype_card]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hcard) hg1) hg2) hχε
end OAI.ActualEisensteinCubic
