-- Prove2me | solution 1 for OAI.CubicJacobiGlobal.symbol_denominator_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:29:49.281202+00:00
-- url     : https://prove2.me/submissions/54b6cc81-5c5f-48b1-b970-f2dbece7f64e

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Theorems.Thm_OAI_CubicRamified_symbol_lambda_congr_mod_nine
import Theorems.Thm_OAI_CubicJacobiGlobal_primary_ne_zero
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_mul_numerator
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_isUnit_ne_zero
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_unit_congr_mod_nine
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_exists_primary_generator
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_congr
import Theorems.Thm_OAI_CubicJacobiGlobal_symbol_reciprocity
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
open scoped BigOperators Classical
namespace CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss
end CubicRamified
namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified
private theorem associated_congr_denominator {x y a b : O} (hxy : Associated x y)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) (hab : (9 : O) ∣ a-b)
    (hy : symbol y a = symbol y b) : symbol x a = symbol x b := by
  obtain ⟨u,hu⟩ := hxy
  apply mul_right_cancel₀ (symbol_isUnit_ne_zero (u : O) a u.isUnit ha)
  calc
    symbol x a * symbol (u : O) a = symbol y a := by
      rw [← symbol_mul_numerator _ _ a ha, hu]
    _ = symbol y b := hy
    _ = symbol x b * symbol (u : O) b := by rw [← hu, symbol_mul_numerator _ _ b hb]
    _ = symbol x b * symbol (u : O) a := by
      rw [symbol_unit_congr_mod_nine (u : O) b a u.isUnit hb ha (by simpa only [neg_sub] using dvd_neg.mpr hab)]
private theorem ramified_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'
private theorem symbol_prime_denominator_congr (p a b : O) (hp : Prime p)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hpab : p ∣ a-b) : symbol p a = symbol p b := by
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  by_cases hg : lambda ∉ (Ideal.span {p} : Ideal O)
  · obtain ⟨q,hq,hprimary,-⟩ := cubicJacobi_exists_primary_generator (Ideal.span {p}) hg
    have hpq : Associated p q := Ideal.span_singleton_eq_span_singleton.mp hq
    apply associated_congr_denominator hpq ha hb h9
    have hq0 : q ≠ 0 := (hpq.prime_iff.mp hp).ne_zero
    rw [symbol_reciprocity q a hq0 (primary_ne_zero a ha) hprimary ha,
      symbol_reciprocity q b hq0 (primary_ne_zero b hb) hprimary hb]
    exact symbol_congr (hpq.dvd'.trans hpab)
  · have hdiv : p ∣ lambda := Ideal.mem_span_singleton.mp (not_not.mp hg)
    apply associated_congr_denominator (hp.associated_of_dvd ramified_prime hdiv) ha hb h9
    exact symbol_lambda_congr_mod_nine a b ha hb h9
end CubicJacobiGlobal
namespace PrimaryIdealUnitReindex
open ActualEisensteinCubic ActualEisensteinCoordinates ShortDraftLatticeCount
end PrimaryIdealUnitReindex
open scoped BigOperators Classical SchwartzMap
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay EisensteinSchwartzPoisson
open PrimaryIdealUnitReindex CompletedGauss
end QuadraticUnitInvariance
namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
end GaussGeneratorTransport
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open QuadraticGaussRay MixedCrossSeparation QuadraticInitialBound
open GaussGeneratorTransport EisensteinSchwartzPoisson
end QuadraticUnitInvariance
open scoped BigOperators Classical SchwartzMap
namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT
end EisensteinSchwartzPoisson
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
open scoped BigOperators Classical
open OAI.CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified
namespace OAI.CubicJacobiGlobal
theorem _root_.solution (x a b : O)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hx : x ∣ a-b) : symbol x a = symbol x b := by
  induction x using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => have heq : a = b := sub_eq_zero.mp (zero_dvd_iff.mp hx); rw [heq]
  | h₂ u hu => exact symbol_unit_congr_mod_nine u a b hu ha hb h9
  | h₃ x p hx0 hp ih =>
    have hpab : p ∣ a-b := (dvd_mul_right p x).trans hx
    have hxab : x ∣ a-b := (dvd_mul_left x p).trans hx
    rw [symbol_mul_numerator _ _ a ha, symbol_mul_numerator _ _ b hb,
      symbol_prime_denominator_congr p a b hp ha hb h9, ih hxab]
    exact hpab
end OAI.CubicJacobiGlobal
