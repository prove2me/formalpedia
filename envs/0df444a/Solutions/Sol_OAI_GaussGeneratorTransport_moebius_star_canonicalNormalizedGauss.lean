-- Prove2me | solution 1 for OAI.GaussGeneratorTransport.moebius_star_canonicalNormalizedGauss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:34.461892+00:00
-- url     : https://prove2.me/submissions/8b5ad736-1ae4-4027-9ea3-0a572402d86f

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Theorems.Thm_OAI_GaussGeneratorTransport_canonicalNormalizedGauss_eq_product
import Theorems.Thm_OAI_FiniteGaussPhase_moebius_star_gauss_one_eq_coefficient


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
open OAI.GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
namespace OAI.GaussGeneratorTransport
theorem _root_.solution {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
      star (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood (fun _ => 1)) =
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) (modulusUnit p : O)) *
        ((canonicalProductG p hp hcop hgood)⁻¹ * canonicalProductCoefficient p hp hcop hgood) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood (fun _ => 1), star_mul]
  calc
    _ = star (finiteSexticRow (fun i => Ideal.span {p i}) hgood (fun _ => 1) (modulusUnit p : O)) *
        ((UniqueFactorizationMonoid.moebius (Ideal.span {∏ i, p i}) : ℂ) *
          star (canonicalProductGauss p hp hcop hgood (fun _ => 1))) := by ring
    _ = _ := by rw [moebius_star_gauss_one_eq_coefficient p hp hcop hgood hchar hprimary]
end OAI.GaussGeneratorTransport
