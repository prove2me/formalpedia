-- Prove2me | solution 1 for OAI.FiniteGaussPhase.canonicalProductCoefficient_mul_gauss_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:31:56.173218+00:00
-- url     : https://prove2.me/submissions/6cca2d1e-21b9-4577-adf8-aa0602d388df

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Theorems.Thm_OAI_FiniteGaussPhase_canonicalProductGauss_one_two_eq_moebius
import Theorems.Thm_OAI_FiniteGaussPhase_angularFactor_mul_star

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
    canonicalProductCoefficient p hp hcop hgood *
      canonicalProductGauss p hp hcop hgood (fun _ => 1) =
      (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
        canonicalProductG p hp hcop hgood := by
  have hα := angularFactor_mul_star (∏ i, p i)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  unfold canonicalProductCoefficient
  calc
    _ = star (angularFactor (∏ i, p i)) *
        (canonicalProductGauss p hp hcop hgood (fun _ => 1) *
          canonicalProductGauss p hp hcop hgood (fun _ => 2)) := by ring
    _ = _ := by
      rw [canonicalProductGauss_one_two_eq_moebius p hp hcop hgood hchar hprimary]
      calc
        _ = (angularFactor (∏ i, p i) * star (angularFactor (∏ i, p i))) *
            ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
              canonicalProductG p hp hcop hgood) := by ring
        _ = _ := by rw [hα, one_mul]
end OAI.FiniteGaussPhase
