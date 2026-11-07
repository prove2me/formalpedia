-- Prove2me | solution 1 for OAI.FiniteGaussPhase.canonicalProductGauss_one_two_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:29:04.877923+00:00
-- url     : https://prove2.me/submissions/7dc3826c-c24a-4e49-a5c2-ec9520229d45

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteGaussPhase_canonicalProductGauss_constant_power
import Theorems.Thm_OAI_FiniteGaussPhase_canonicalCrossFactor_pow_six
import Theorems.Thm_OAI_ActualEisensteinCubic_breveGamma1_gamma2_relation
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
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductGauss p hp hcop hgood (fun _ => 1) *
      canonicalProductGauss p hp hcop hgood (fun _ => 2) =
      canonicalProductG p hp hcop hgood *
        canonicalProductGauss p hp hcop hgood (fun _ => 2) ^ 3 := by
  let g (j : ℕ) (i : ι) := ConcreteBreveE.normalizedTraceGauss (p i) (hp i)
    (canonicalSextic (Ideal.span {p i}) (hgood i) ^ j)
  let v (i : ι) := canonicalSextic (Ideal.span {p i}) (hgood i)
    (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O))
  have hlocal (i : ι) : g 1 i * g 2 i = (v i)⁻¹ * g 3 i * (g 2 i) ^ 3 := by
    simpa only [g, v, pow_one, ConcreteBreveE.normalizedTraceGauss,
      breveGamma1, breveGamma2, breveGamma3] using
      breveGamma1_gamma2_relation (Ideal.span {p i}) (hgood i) (hchar i)
        (p i) rfl (hp i) (hprimary i)
  have hprod : (∏ i, g 1 i) * (∏ i, g 2 i) =
      (∏ i, v i)⁻¹ * (∏ i, g 3 i) * (∏ i, g 2 i) ^ 3 := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [hlocal]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, Finset.prod_pow]
  rw [canonicalProductG,
    canonicalProductGauss_constant_power p hp hcop hgood 1 (by decide),
    canonicalProductGauss_constant_power p hp hcop hgood 2 (by decide),
    canonicalProductGauss_constant_power p hp hcop hgood 3 (by decide)]
  change (canonicalCrossFactor p hgood ^ 1 * ∏ i, g 1 i) *
    (canonicalCrossFactor p hgood ^ 2 * ∏ i, g 2 i) =
    ((∏ i, v i)⁻¹ * (canonicalCrossFactor p hgood ^ 3 * ∏ i, g 3 i)) *
      (canonicalCrossFactor p hgood ^ 2 * ∏ i, g 2 i) ^ 3
  rw [mul_pow, ← pow_mul]
  change _ = _ * (canonicalCrossFactor p hgood ^ 6 * _)
  rw [canonicalCrossFactor_pow_six p hcop hgood, one_mul]
  calc
    _ = canonicalCrossFactor p hgood ^ 3 * ((∏ i, g 1 i) * ∏ i, g 2 i) := by ring
    _ = _ := by rw [hprod]; ring
end OAI.FiniteGaussPhase
