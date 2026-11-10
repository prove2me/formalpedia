-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.columnSquareFiber_all_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:25:15.103269+00:00
-- url     : https://prove2.me/submissions/16dfb2f2-bf69-4402-8865-aa5930461158

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_CanonicalQuadraticSieve_squarefree_all_column_energy
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnSquareFiber_nonzero_bounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_quadraticRow_primary_squarefree
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnSquareFiber_injective


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
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (S : Finset (Ideal O)) (X K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X)
    (A : Ideal O) (a : Ideal O → ℂ) :
    (∑k : idealRange K, ‖∑I∈columnSquareFiber S A,
      quadraticRow k.val (primaryGenerator I)*a I‖^2) ≤
      4*sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K *
        ∑I∈columnSquareFiber S A,‖a I‖^2 := by
  let T := columnSquareFiber S A
  have he := squarefree_all_column_energy
    (fun I : T => squarefreePart I.val) (columnSquareFiber_injective S A)
    (X/(Ideal.absNorm A:ℝ)^2) K (fun I => columnSquareFiber_nonzero_bounds S X hS A I)
    (fun I : T => a I.val)
  have hm (k : idealRange K) :
      ‖∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val‖^2 ≤
        ‖∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val‖^2 := by
    have hrow : (∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val)=
        idealZeroMask k.val (primaryGenerator A)*
        ∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      have hi := (Finset.mem_filter.mp I.property).2
      have hq : quadraticRow k.val (primaryGenerator I.val)=
          idealZeroMask k.val (primaryGenerator A)*quadraticRow k.val (primaryGenerator (squarefreePart I.val)) := by
        have hh := canonical_quadraticRow_primary_squarefree k.val (mem_idealRange.mp k.property).1
          (squarePart I.val) (squarefreePart I.val)
        rw [squarePart_sq_mul_squarefreePart,hi] at hh
        exact hh
      rw [hq]
      ring
    rw [hrow,norm_mul,mul_pow]
    have hmask : ‖idealZeroMask k.val (primaryGenerator A)‖^2≤1 := by
      unfold idealZeroMask
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (sq_nonneg _) hmask
  have hr (k : idealRange K) :
      (∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val :=
    (Finset.sum_coe_sort T _).symm
  simp_rw [hr]
  rw [←Finset.sum_coe_sort T (fun I => ‖a I‖^2)]
  exact (Finset.sum_le_sum (fun k _ => hm k)).trans
    he
end OAI.CanonicalQuadraticSieve
