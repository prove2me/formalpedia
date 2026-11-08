-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.highKernel_energy_le_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:14:10.126971+00:00
-- url     : https://prove2.me/submissions/b70099ed-67ad-4586-afbf-52f2b001a344

import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_TupleWeights
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
import Theorems.Thm_OAI_CanonicalQuadraticSieve_mem_highKernelRange
import Theorems.Thm_OAI_QuadraticInitialBound_sieveBump_eq_one


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
open scoped BigOperators
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N K : ℝ) (hM : 0 < M) (a : idealRange N → ℂ) :
    (∑ I : highKernelRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      smoothHighEnergy M N K a := by
  let E : Ideal O → ℝ := fun I => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖ ^ 2
  have hsub : highKernelRange M K ⊆ highKernelRange (2 * M) K := by
    intro I hI
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp hI
    exact mem_highKernelRange.mpr ⟨hs, by linarith, hk⟩
  have hv (I : Ideal O) (hI : I ∈ highKernelRange M K) : smoothHighWeight M I = 1 := by
    apply QuadraticInitialBound.sieveBump_eq_one (div_nonneg (Nat.cast_nonneg _) hM.le)
    exact (div_le_one hM).mpr (mem_highKernelRange.mp hI).2.1
  change (∑ I : highKernelRange M K, E I.val) ≤
    ∑ I : highKernelRange (2 * M) K, smoothHighWeight M I.val * E I.val
  rw [Finset.sum_coe_sort (highKernelRange M K) E,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => smoothHighWeight M I * E I)]
  calc
    _ = ∑ I ∈ highKernelRange M K, smoothHighWeight M I * E I :=
      Finset.sum_congr rfl (fun I hI => by rw [hv I hI, one_mul])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I hI hnot =>
      mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _))
end OAI.CanonicalQuadraticSieve
