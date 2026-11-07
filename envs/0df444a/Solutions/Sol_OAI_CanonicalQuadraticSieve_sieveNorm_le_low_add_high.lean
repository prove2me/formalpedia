-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.sieveNorm_le_low_add_high
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:25:31.392948+00:00
-- url     : https://prove2.me/submissions/5ade3ac5-6112-4fa0-807d-d6391b342315

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DivisorBlocks
import Theorems.Thm_OAI_FiniteSieveRestriction_squared_norm_row_partition
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_supported
import Theorems.Thm_OAI_CanonicalQuadraticSieve_squarefreePart_eq_self
import Theorems.Thm_OAI_CanonicalQuadraticSieve_mem_highKernelRange
import Theorems.Thm_OAI_CanonicalQuadraticSieve_family_squared_norm_le
import Theorems.Thm_OAI_FiniteSieveRestriction_submatrix_norm_le


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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel FiniteSieveOperator
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N K : ℝ) :
    sieveNorm M N ≤ sieveNorm K N + highKernelNorm M N K := by
  let P : idealRange M → Prop := fun I => (Ideal.absNorm I.val : ℝ) ≤ K
  let lo := {I : idealRange M // P I}
  let hi := {I : idealRange M // ¬ P I}
  have hlo : ‖operator (fun (I : lo) (J : idealRange N) => matrix M N I.val J)‖ ^ 2 ≤
      sieveNorm K N := by
    apply family_squared_norm_le (fun I : lo => I.val.val) (fun J : idealRange N => J.val)
    · intro I J h
      apply Subtype.ext
      exact Subtype.ext h
    · exact Subtype.val_injective
    · intro I
      exact ⟨(mem_idealRange.mp I.val.property).1, I.property⟩
    · intro J
      exact mem_idealRange.mp J.property
  let toHigh : hi → highKernelRange M K := fun I => ⟨I.val.val, by
    apply mem_highKernelRange.mpr
    have hI := mem_idealRange.mp I.val.property
    refine ⟨admissible_supported hI.1, hI.2, ?_⟩
    rw [squarefreePart_eq_self hI.1.2.1]
    exact lt_of_not_ge I.property⟩
  have hhighinj : Function.Injective toHigh := by
    intro I J h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : highKernelRange M K => I.val) h
  have hhi := FiniteSieveRestriction.submatrix_norm_le toHigh hhighinj
    (fun J : idealRange N => J) Function.injective_id (highKernelMatrix M N K)
  have hhisq : ‖operator (fun (I : hi) (J : idealRange N) => matrix M N I.val J)‖ ^ 2 ≤
      highKernelNorm M N K := pow_le_pow_left₀ (norm_nonneg _) hhi 2
  exact (FiniteSieveRestriction.squared_norm_row_partition (matrix M N) P).trans (add_le_add hlo hhisq)
end OAI.CanonicalQuadraticSieve
