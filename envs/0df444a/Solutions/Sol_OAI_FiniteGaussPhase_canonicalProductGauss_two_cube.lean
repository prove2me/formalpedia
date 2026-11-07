-- Prove2me | solution 1 for OAI.FiniteGaussPhase.canonicalProductGauss_two_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:29:04.123227+00:00
-- url     : https://prove2.me/submissions/10d8fd9a-8dbe-43be-8b25-300ea31cad6c

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteGaussPhase_canonicalProductGauss_constant_power
import Theorems.Thm_OAI_FiniteGaussPhase_angularFactor_prod
import Theorems.Thm_OAI_FiniteGaussPhase_canonicalCrossFactor_pow_six
import Theorems.Thm_OAI_FiniteGaussPhase_product_moebius_eq_sign
import Theorems.Thm_OAI_ActualEisensteinCubic_breveGamma2_cube
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk

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
open scoped BigOperators Classical
open OAI.FiniteGaussPhase
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.FiniteGaussPhase
theorem _root_.solution {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductGauss p hp hcop hgood (fun _ => 2) ^ 3 =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        angularFactor (∏ i, p i) := by
  have hlocal (i : ι) :
      ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
        (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2) ^ 3 =
        -angularFactor (p i) := by
    change breveGamma2 (Ideal.span {p i}) (hgood i) (p i) rfl (hp i) ^ 3 = _
    simpa only [angularFactor, neg_div] using
      breveGamma2_cube (Ideal.span {p i}) (hgood i) (p i) rfl (hp i) (hprimary i)
  rw [canonicalProductGauss_constant_power p hp hcop hgood 2 (by decide),
    mul_pow, ← pow_mul]
  change canonicalCrossFactor p hgood ^ 6 * _ = _
  rw [canonicalCrossFactor_pow_six p hcop hgood, one_mul, ← Finset.prod_pow]
  simp_rw [hlocal]
  rw [Finset.prod_neg, product_moebius_eq_sign p hcop, angularFactor_prod]
  rfl
end OAI.FiniteGaussPhase
