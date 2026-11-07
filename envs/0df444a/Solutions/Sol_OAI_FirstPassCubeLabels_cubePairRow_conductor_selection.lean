-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.cubePairRow_conductor_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:30.559395+00:00
-- url     : https://prove2.me/submissions/122cc252-089b-42c6-9dc4-4511a1df7437

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Theorems.Thm_OAI_FirstPassCubeLabels_cubePairLocal_eq_character
import Theorems.Thm_OAI_FirstPassCubeLabels_cubePairRow_eq_product
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


section
namespace OAI
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
namespace FiniteSieveOperator
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
end FiniteSieveOperator
section
open scoped BigOperators Classical
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT RayFourExpansion
end QuadraticInitialBound
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum UniqueFactorizationMonoid
namespace IdealDivisorBound
end IdealDivisorBound
end
namespace SecondPassFiber
open scoped BigOperators Classical
open IdealMobiusDivisorSum ConcretePrimeRowBridge
end SecondPassFiber
open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic
private theorem principal_product_eq_mask {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (B : Finset κ) (z : O) :
    (∏ j ∈ B, (1 : MulChar (O ⧸ P j) ℂ) (Ideal.Quotient.mk (P j) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ j ∈ B, z ∈ P j
  · rw [rowCoprimeMask, if_pos h]
    obtain ⟨j, hj, hz⟩ := h
    apply Finset.prod_eq_zero hj
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · rw [rowCoprimeMask, if_neg h]
    apply Finset.prod_eq_one
    intro j hj
    apply MulChar.one_apply
    let : Field (O ⧸ P j) := Ideal.Quotient.field (P j)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨j, hj, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩
open scoped SchwartzMap ContDiff
open ConcreteTraceCRT
open EisensteinSchwartzPoisson (paperRadialFourier)
end FirstPassCubeLabels
end
end OAI
end

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
theorem _root_.solution {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hcover : ∀ j ∈ B, 0 < v₁ j + v₂ j + bit (ε₁ j) + bit (ε₂ j)) (z : O) :
    cubePairRow P hg B v₁ v₂ ε₁ ε₂ z =
      rowCoprimeMask P (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
        finiteSexticRow (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)
          (fun j => hg j.val)
          (fun j => (conductorExponent (parity (v₁ j.val + v₂ j.val))
            (ε₁ j.val) (ε₂ j.val)).val) z := by
  let e := fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j)
  let f := fun j => (canonicalSextic (P j) (hg j) ^ (e j).val) (Ideal.Quotient.mk (P j) z)
  have hlocal : cubePairRow P hg B v₁ v₂ ε₁ ε₂ z = ∏ j ∈ B, f j := by
    rw [cubePairRow_eq_product]
    apply Finset.prod_congr rfl
    intro j hj
    exact cubePairLocal_eq_character (P j) (hg j) (v₁ j) (v₂ j)
      (ε₁ j) (ε₂ j) (hcover j hj) z
  have hzero : (∏ j ∈ B.filter (fun j => e j = 0), f j) =
      rowCoprimeMask P (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro j hj
    have he : e j = 0 := (Finset.mem_filter.mp hj).2
    simp only [f, he, ZMod.val_zero, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B (fun j => e j = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := cubeConductorSupport B v₁ v₂ ε₁ ε₂) (f := f)).symm
end OAI.FirstPassCubeLabels
