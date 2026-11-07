-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finiteSquarefreeRow_mean_square_mobius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:41.287872+00:00
-- url     : https://prove2.me/submissions/80f9daf4-bc7c-4e16-8ab2-8a111d7683d4

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_pair_sum_mobius
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace ActualEisensteinCubic
section
open scoped ComplexConjugate
end
private theorem finite_energy_expand {α β : Type*}
    (R : Finset α) (C : Finset β) (V : α → ℂ) (a : β → ℂ)
    (r : β → α → ℂ) :
    (∑ u ∈ R, V u * (↑(‖∑ n ∈ C, a n * r n u‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, star (a n) * a m *
        ∑ u ∈ R, V u * star (r n u) * r m u := by
  have hnorm (u : α) :
      (↑(‖∑ n ∈ C, a n * r n u‖ ^ 2) : ℂ) =
        (∑ n ∈ C, star (a n) * star (r n u)) *
          (∑ m ∈ C, a m * r m u) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, starRingEnd_apply]
  simp_rw [hnorm]
  calc
    _ = ∑ u ∈ R, ∑ n ∈ C, ∑ m ∈ C,
        (star (a n) * a m) * (V u * star (r n u) * r m u) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
end ActualEisensteinCubic
namespace ConcretePrimeRowBridge
section
open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped BigOperators Classical
end
open ActualEisensteinCubic
end ConcretePrimeRowBridge
namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace
end EisensteinSchwartzPoisson
end
end OAI
end

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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι β : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (C : Finset β) (support : β → Finset ι) (a : β → ℂ)
    (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * (↑(‖∑ n ∈ C,
      a n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, star (a n) * a m *
        ∑ E ∈ (support n ∩ support m).powerset, (-1 : ℂ) ^ E.card *
          ∑ u ∈ R.filter (fun u => ∀ i ∈ E, u ∈ P i),
            V u * star (finiteSquarefreeRow P hgood (support n \ support m) u) *
              finiteSquarefreeRow P hgood (support m \ support n) u := by
  rw [finite_energy_expand]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  exact finiteSquarefreeRow_pair_sum_mobius P hgood (support n) (support m) R V
end OAI.ActualEisensteinCubic
