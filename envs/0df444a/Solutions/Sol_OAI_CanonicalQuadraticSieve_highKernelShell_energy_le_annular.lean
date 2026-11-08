-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.highKernelShell_energy_le_annular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:19:04.174534+00:00
-- url     : https://prove2.me/submissions/6b903959-7715-44f4-976e-e31cd41c2ea2

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularRecursion
import Theorems.Thm_OAI_CanonicalQuadraticSieve_mem_highKernelShellRange
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveBump_eq_one
import Theorems.Thm_OAI_CanonicalQuadraticSieve_mem_highKernelRange


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
open scoped SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N K : ℝ) (hM : 0 < M) (a : idealRange N → ℂ) :
    (∑ I : highKernelShellRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      annularHighEnergy M N K a := by
  let E : Ideal O → ℝ := fun I => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖ ^ 2
  have hsub : highKernelShellRange M K ⊆ highKernelRange (2 * M) K := by
    intro I hI
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp (mem_highKernelShellRange.mp hI).1
    exact mem_highKernelRange.mpr ⟨hs, by linarith, hk⟩
  have hv (I : Ideal O) (hI : I ∈ highKernelShellRange M K) : annularHighWeight M I = 1 := by
    apply QuadraticInitialBound.annularSieveBump_eq_one
    · apply (le_div_iff₀ hM).mpr
      have h := (mem_highKernelShellRange.mp hI).2
      linarith
    · exact (div_le_one hM).mpr (mem_highKernelRange.mp (mem_highKernelShellRange.mp hI).1).2.1
  change (∑ I : highKernelShellRange M K, E I.val) ≤
    ∑ I : highKernelRange (2 * M) K, annularHighWeight M I.val * E I.val
  rw [Finset.sum_coe_sort (highKernelShellRange M K) E,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => annularHighWeight M I * E I)]
  calc
    _ = ∑ I ∈ highKernelShellRange M K, annularHighWeight M I * E I :=
      Finset.sum_congr rfl (fun I hI => by rw [hv I hI, one_mul])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I hI hnot =>
      mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (sq_nonneg _))
end OAI.CanonicalQuadraticSieve
