-- Prove2me | solution 1 for OAI.QuadraticInitialBound.quadraticSymbol_reciprocity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:16:43.183364+00:00
-- url     : https://prove2.me/submissions/d55088a0-5988-48fc-883e-aec2cf03018c

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Theorems.Thm_OAI_QuadraticInitialBound_quadraticSymbol_mul_reverse
import Theorems.Thm_OAI_QuadraticInitialBound_quadraticSymbol_eq_zero_of_not_disjoint
import Theorems.Thm_OAI_QuadraticInitialBound_quadraticSymbol_sq_eq_one
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
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open FiniteGaussPhase MixedCrossSeparation ActualEisensteinCoordinates QuadraticGaussRay
open RayFourExpansion
namespace OAI.QuadraticInitialBound
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A B : Finset ι) :
    quadraticSymbol p hg A B =
      quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) *
        quadraticSymbol p hg B A := by
  by_cases hd : Disjoint A B
  · have hprod := quadraticSymbol_mul_reverse p hg A B
    rw [quadraticCrossPhase_eq_rayPair p hp hcop hg hc A B hd] at hprod
    have hsq := quadraticSymbol_sq_eq_one p hcop hg B A hd.symm
    calc
      _ = quadraticSymbol p hg A B * (quadraticSymbol p hg B A) ^ 2 := by rw [hsq, mul_one]
      _ = _ := by rw [pow_two, ← mul_assoc, hprod]
  · rw [quadraticSymbol_eq_zero_of_not_disjoint p hg A B hd,
      quadraticSymbol_eq_zero_of_not_disjoint p hg B A (fun h => hd h.symm), mul_zero]
end OAI.QuadraticInitialBound
