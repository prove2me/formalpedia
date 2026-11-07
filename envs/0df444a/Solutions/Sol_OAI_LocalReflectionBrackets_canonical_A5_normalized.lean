-- Prove2me | solution 1 for OAI.LocalReflectionBrackets.canonical_A5_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:22:05.425222+00:00
-- url     : https://prove2.me/submissions/762f7897-ce6d-4855-aa45-b6ee3efb6953

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Theorems.Thm_OAI_LocalReflectionBrackets_rootCard_pos
import Theorems.Thm_OAI_LocalReflectionBrackets_rootCard_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jfour
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jzero_active
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_nonexceptional
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



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
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped Classical BigOperators
open AddChar MulChar
open scoped Classical BigOperators
open AddChar MulChar
open OAI.LocalReflectionBrackets
variable {F : Type*} [Field F] [Fintype F]
open ActualEisensteinCubic
attribute [local instance] OAI.LocalReflectionBrackets.quotientFieldNormalized
attribute [local instance] OAI.LocalReflectionBrackets.quotientFintypeNormalized
namespace OAI.LocalReflectionBrackets
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    activeRow (canonicalSextic P hgood) ψ j σ ε x =
      (((canonicalSextic P hgood)⁻¹) ^ 2) σ *
        phase (canonicalSextic P hgood) ψ j ε * bracket (canonicalSextic P hgood) j x := by
  let χ := canonicalSextic P hgood
  have hψne : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ (a := 1) one_ne_zero
  have hr : (rootCard (O ⧸ P) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard (O ⧸ P) : ℂ) ^ 2 = (Fintype.card (O ⧸ P) : ℂ) := by
    exact_mod_cast (rootCard_sq (F := O ⧸ P))
  by_cases hj0 : j = 0
  · subst j
    have hh := canonical_A5_jzero_active P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte]
    rw [← hsq]
    field_simp
  by_cases hj4 : j = 4
  · subst j
    have hh := canonical_A5_jfour P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    have hqNat : 1 ≤ Fintype.card (O ⧸ P) := Fintype.card_pos_iff.mpr ⟨0⟩
    have hcardunits : (Fintype.card (O ⧸ P)ˣ : ℂ) = (Fintype.card (O ⧸ P) : ℂ) - 1 := by
      rw [Fintype.card_units, Nat.cast_sub hqNat, Nat.cast_one]
    have hsum : (if (ε : O ⧸ P) * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1) =
        -1 + (Fintype.card (O ⧸ P) : ℂ) * if x = 0 then 1 else 0 := by
      by_cases hx : x = 0
      · simp [hx, hcardunits]
        ring
      · simp [hx, mul_ne_zero (Units.ne_zero ε) hx]
    rw [hsum]
    simp only [phase, bracket, tau,  ↓reduceIte]
    rw [← hsq]
    field_simp
  · have hh := canonical_A5_nonexceptional P hgood hchar ψ j hj0 hj6 hj4 σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, if_neg hj4, if_neg hj0]
    rw [← hsq]
    field_simp
end OAI.LocalReflectionBrackets
