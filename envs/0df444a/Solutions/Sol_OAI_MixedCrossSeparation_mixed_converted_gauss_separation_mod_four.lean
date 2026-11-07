-- Prove2me | solution 1 for OAI.MixedCrossSeparation.mixed_converted_gauss_separation_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:08.473925+00:00
-- url     : https://prove2.me/submissions/67be36b8-5fc7-4ff2-ad8d-757e180f4e8b

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
import Theorems.Thm_OAI_MixedCrossSeparation_mixed_converted_gauss_separation
import Theorems.Thm_OAI_MixedCrossSeparation_quadraticCrossPhase_eq_rayPair

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
open OAI.MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates
namespace OAI.MixedCrossSeparation
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (inverse : ι → Bool) (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    (∏ i, ∏ k ∈ Finset.univ.erase i,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if inverse i then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k))) *
      (∏ i, convertedLocal (p i) (hp i) (hg i) (inverse i)) =
    convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = true) true *
      convertedColumnBlock p hp hg (Finset.univ.filter fun i => inverse i = false) false *
      quadraticRayPair
        (residue (∏ i ∈ Finset.univ.filter (fun i => inverse i = true), p i))
        (residue (∏ i ∈ Finset.univ.filter (fun i => inverse i = false), p i)) := by
  rw [mixed_converted_gauss_separation p hp hg inverse hprimary]
  congr 1
  apply quadraticCrossPhase_eq_rayPair p hp hcop hg hchar
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have ht := (Finset.mem_filter.mp hi).2
  have hf := (Finset.mem_filter.mp hj).2
  rw [ht] at hf
  contradiction
end OAI.MixedCrossSeparation
