-- Prove2me | solution 1 for OAI.FiniteGaussPhase.moebius_star_gauss_one_eq_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:32:58.012144+00:00
-- url     : https://prove2.me/submissions/611d1180-385a-4a00-bd64-01a35ed8920a

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Theorems.Thm_OAI_FiniteGaussPhase_canonicalProductGauss_one_two_eq_moebius
import Theorems.Thm_OAI_FiniteGaussPhase_angularFactor_mul_star
import Theorems.Thm_OAI_FiniteGaussPhase_norm_canonicalProductGauss
import Theorems.Thm_OAI_FiniteGaussPhase_norm_canonicalProductG

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
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) =
      (canonicalProductG p hp hcop hgood)⁻¹ * canonicalProductCoefficient p hp hcop hgood := by
  have hα := angularFactor_mul_star (∏ i, p i)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hg : canonicalProductGauss p hp hcop hgood (fun _ => 1) *
      star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj',
      norm_canonicalProductGauss p hp hcop hgood hchar (fun _ => 1)
        (by intro; decide) (by intro; decide)]
    norm_num
  have hG : canonicalProductG p hp hcop hgood ≠ 0 := by
    intro hz
    have hn := norm_canonicalProductG p hp hcop hgood hchar hprimary
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have hA : canonicalProductCoefficient p hp hcop hgood =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
          canonicalProductG p hp hcop hgood := by
    unfold canonicalProductCoefficient
    calc
      _ = star (angularFactor (∏ i, p i)) *
          star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
            (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
              canonicalProductGauss p hp hcop hgood (fun _ => 2)) := by
        calc
          _ = (star (angularFactor (∏ i, p i)) *
              canonicalProductGauss p hp hcop hgood (fun _ => 2)) * 1 := by ring
          _ = _ := by rw [← hg]; ring
      _ = _ := by
        rw [canonicalProductGauss_one_two_eq_moebius p hp hcop hgood hchar hprimary]
        calc
          _ = (angularFactor (∏ i, p i) * star (angularFactor (∏ i, p i))) *
              ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
                star (canonicalProductGauss p hp hcop hgood (fun _ => 1)) *
                  canonicalProductG p hp hcop hgood) := by ring
          _ = _ := by rw [hα, one_mul]
  rw [hA]
  field_simp
end OAI.FiniteGaussPhase
