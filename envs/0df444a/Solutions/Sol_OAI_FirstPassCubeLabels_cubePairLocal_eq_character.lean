-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.cubePairLocal_eq_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:20:56.943011+00:00
-- url     : https://prove2.me/submissions/6bec25c2-d827-447b-ad74-51122e193ea6

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Theorems.Thm_OAI_FirstPassCubeLabels_cube_pair_exponent_mod
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_conj_as_row_label
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_sixth_power_mask
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
open scoped BigOperators
open scoped BigOperators Classical
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
namespace OAI.FirstPassCubeLabels
theorem _root_.solution
    (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m₁ + m₂ + bit ε₁ + bit ε₂) (z : O) :
    cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      (canonicalSextic P hg ^ (conductorExponent (parity (m₁ + m₂)) ε₁ ε₂).val)
        (Ideal.Quotient.mk P z) := by
  let q := canonicalSextic P hg (Ideal.Quotient.mk P z)
  have hstar : star q = q ^ 5 := by
    have hs := canonicalSextic_conj_as_row_label P hg z
    change star q = q * q ^ 4 at hs
    rw [hs]
    ring
  have hleft : cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      q ^ (bit ε₁ + 5 * bit ε₂ + 3 * m₁ + 15 * m₂) := by
    change q ^ bit ε₁ * star (q ^ bit ε₂) * q ^ (3 * m₁) * star (q ^ (3 * m₂)) = _
    simp only [star_pow, hstar, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hleft]
  by_cases hz : z ∈ P
  · have hq : q = 0 := by
      change canonicalSextic P hg (Ideal.Quotient.mk P z) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    rw [hq, Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    exact zero_pow (by omega)
  · have hu : IsUnit (Ideal.Quotient.mk P z) := by
      let : Field (O ⧸ P) := Ideal.Quotient.field P
      exact isUnit_iff_ne_zero.mpr (fun h => hz (Ideal.Quotient.eq_zero_iff_mem.mp h))
    have h6 : q ^ 6 = 1 := by
      have h := canonicalSextic_sixth_power_mask P hg z
      simp only [map_pow, if_neg hz] at h
      exact h
    rw [pow_eq_pow_mod _ h6, cube_pair_exponent_mod]
    exact (MulChar.pow_apply_coe _ _ hu.unit).symm
end OAI.FirstPassCubeLabels
