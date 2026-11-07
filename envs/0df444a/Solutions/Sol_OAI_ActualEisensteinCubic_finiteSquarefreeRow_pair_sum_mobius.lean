-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finiteSquarefreeRow_pair_sum_mobius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:58:14.458234+00:00
-- url     : https://prove2.me/submissions/33d86f0b-a278-434e-8921-729283df188b

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_pair_kernel
import Theorems.Thm_OAI_ActualEisensteinCubic_rowCoprimeMask_subsets
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
    {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S T : Finset ι) (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * star (finiteSquarefreeRow P hgood S u) *
      finiteSquarefreeRow P hgood T u) =
      ∑ E ∈ (S ∩ T).powerset, (-1 : ℂ) ^ E.card *
        ∑ u ∈ R.filter (fun u => ∀ i ∈ E, u ∈ P i),
          V u * star (finiteSquarefreeRow P hgood (S \ T) u) *
            finiteSquarefreeRow P hgood (T \ S) u := by
  classical
  have hterm (u : O) :
      V u * star (finiteSquarefreeRow P hgood S u) *
          finiteSquarefreeRow P hgood T u =
        ∑ E ∈ (S ∩ T).powerset, (-1 : ℂ) ^ E.card *
          if ∀ i ∈ E, u ∈ P i then
            V u * star (finiteSquarefreeRow P hgood (S \ T) u) *
              finiteSquarefreeRow P hgood (T \ S) u else 0 := by
    rw [mul_assoc, finiteSquarefreeRow_pair_kernel, rowCoprimeMask_subsets]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro E hE
    by_cases h : ∀ i ∈ E, u ∈ P i
    · simp only [if_pos h, mul_one]
      ring
    · simp only [if_neg h, mul_zero, zero_mul]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : ∀ i ∈ E, u ∈ P i <;> simp [h]
end OAI.ActualEisensteinCubic
