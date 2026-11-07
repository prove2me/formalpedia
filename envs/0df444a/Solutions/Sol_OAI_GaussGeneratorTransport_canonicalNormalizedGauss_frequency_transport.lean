-- Prove2me | solution 1 for OAI.GaussGeneratorTransport.canonicalNormalizedGauss_frequency_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:24:10.609247+00:00
-- url     : https://prove2.me/submissions/549cb404-9d2d-4de9-ad15-4e54d7e6d690

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Theorems.Thm_OAI_GaussGeneratorTransport_finiteSexticRow_unit_mul_star
import Theorems.Thm_OAI_GaussGeneratorTransport_canonicalNormalizedGauss_eq_product
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSexticRow_mul


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
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (j : ι → ℕ) (h : O) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hgood j *
      star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j ((modulusUnit p : O) * h)) =
      canonicalProductGauss p hp hcop hgood j *
        star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hgood j,
    finiteSexticRow_mul, star_mul]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O) *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j (modulusUnit p : O))) *
        (canonicalProductGauss p hp hcop hgood j *
          star (finiteSexticRow (fun i => Ideal.span {p i}) hgood j h)) := by ring
    _ = _ := by rw [finiteSexticRow_unit_mul_star, one_mul]
end OAI.GaussGeneratorTransport
