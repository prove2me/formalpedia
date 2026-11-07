-- Prove2me | solution 1 for OAI.MixedCrossSeparation.quadraticCrossPhase_eq_rayPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:16:03.308212+00:00
-- url     : https://prove2.me/submissions/c5966431-9d7d-4bae-be34-0e176b154a7a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
import Theorems.Thm_OAI_MixedCrossSeparation_quadraticBlock_eq_rayValue
import Theorems.Thm_OAI_MixedCrossSeparation_quadraticBlock_union
import Theorems.Thm_OAI_MixedCrossSeparation_norm_quadraticBlock
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_mul


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
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B =
      quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) := by
  have hA0 : quadraticBlock p hp hg A ≠ 0 := by
    intro hz
    have hn := norm_quadraticBlock p hp hcop hg hchar A
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have hB0 : quadraticBlock p hp hg B ≠ 0 := by
    intro hz
    have hn := norm_quadraticBlock p hp hcop hg hchar B
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have h := quadraticBlock_union p hp hg A B hd
  have hdiv : quadraticCrossPhase p hg A B = quadraticBlock p hp hg (A ∪ B) /
      (quadraticBlock p hp hg A * quadraticBlock p hp hg B) := by
    apply (eq_div_iff (mul_ne_zero hA0 hB0)).mpr
    rw [h]
    ring
  rw [hdiv, quadraticBlock_eq_rayValue p hp hcop hg hchar (A ∪ B),
    quadraticBlock_eq_rayValue p hp hcop hg hchar A,
    quadraticBlock_eq_rayValue p hp hcop hg hchar B, Finset.prod_union hd,
    residue_mul]
  rfl
end OAI.MixedCrossSeparation
