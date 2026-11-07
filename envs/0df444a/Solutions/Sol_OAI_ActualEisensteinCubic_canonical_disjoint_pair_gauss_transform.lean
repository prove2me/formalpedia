-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_disjoint_pair_gauss_transform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:22:11.923366+00:00
-- url     : https://prove2.me/submissions/5e42d9d5-8eee-4161-aae9-30e5b108f48c

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_finite_prime_gauss_transform_scalar

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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S : Finset ι) (ψ : AddChar (O ⧸ ∏ i, P i) ℂ)
    (h : O ⧸ ∏ i, P i) :
    let row := finiteSexticQuotientRow P hc hgood (fun i => if i ∈ S then 1 else 5)
    (∑ x : O ⧸ ∏ i, P i, row x * ψ (h * x)) =
      (row h)⁻¹ * ∑ x : O ⧸ ∏ i, P i, row x * ψ x := by
  classical
  exact canonical_finite_prime_gauss_transform_scalar P hc hgood hchar
    (fun i => if i ∈ S then 1 else 5)
    (fun i => by split_ifs <;> decide)
    (fun i => by split_ifs <;> decide) ψ h
end OAI.ActualEisensteinCubic
