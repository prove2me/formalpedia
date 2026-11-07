-- Prove2me | solution 1 for OAI.QuadraticUnitInvariance.quadraticBlock_union_eq_one_of_same_ray
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:12:11.026359+00:00
-- url     : https://prove2.me/submissions/c13ce71a-4b3a-45ba-952e-0a28007bf3e8

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Theorems.Thm_OAI_QuadraticUnitInvariance_odd_of_quadraticRayValue_norm_eq_one
import Theorems.Thm_OAI_MixedCrossSeparation_norm_quadraticBlock
import Theorems.Thm_OAI_MixedCrossSeparation_quadraticBlock_eq_rayValue
import Theorems.Thm_OAI_QuadraticGaussRay_quadraticRayValue_same_residue_product


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
open scoped BigOperators Classical SchwartzMap
open OAI.QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open QuadraticGaussRay MixedCrossSeparation QuadraticInitialBound
open GaussGeneratorTransport EisensteinSchwartzPoisson
namespace OAI.QuadraticUnitInvariance
theorem _root_.solution
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B)
    (hray : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i)) :
    quadraticBlock p hp hg (A ∪ B) = 1 := by
  have hnorm := norm_quadraticBlock p hp hcop hg hchar A
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar A] at hnorm
  have hodd := odd_of_quadraticRayValue_norm_eq_one _ hnorm
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar (A ∪ B), Finset.prod_union hd]
  exact quadraticRayValue_same_residue_product _ _ hodd hray
end OAI.QuadraticUnitInvariance
