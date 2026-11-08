-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.highKernel_dyadic_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:22:04.96603+00:00
-- url     : https://prove2.me/submissions/03795822-cd95-4ee3-b2db-45ffc5222234

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularRecursion
import Theorems.Thm_OAI_CanonicalQuadraticSieve_mem_highKernelShellRange
import Theorems.Thm_OAI_CanonicalQuadraticSieve_exists_dyadic_shell
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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M K : ℝ) (lengthScale : ℕ) (hML : M ≤ (2 : ℝ) ^ lengthScale)
    (I : Ideal O) (hI : I ∈ highKernelRange M K) :
    ∃ j ∈ Finset.range (lengthScale + 1), I ∈ highKernelShellRange ((2 : ℝ) ^ j) K := by
  obtain ⟨hs, hN, hk⟩ := mem_highKernelRange.mp hI
  have hn : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hs.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨j, hj, hlo, hhi⟩ := exists_dyadic_shell (Ideal.absNorm I) lengthScale hn (hN.trans hML)
  exact ⟨j, hj, mem_highKernelShellRange.mpr ⟨mem_highKernelRange.mpr ⟨hs, hhi, hk⟩, hlo⟩⟩
end OAI.CanonicalQuadraticSieve
