-- Prove2me | solution 1 for OAI.FiniteSieveOperator.separated_phase_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:19:21.320953+00:00
-- url     : https://prove2.me/submissions/599d71cd-f279-4c66-a169-4ae712506031

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Theorems.Thm_OAI_FiniteSieveOperator_operator_smul
import Theorems.Thm_OAI_FiniteSieveOperator_operator_sum
import Theorems.Thm_OAI_FiniteSieveOperator_diagonal_twist_norm_le

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
open OAI.FiniteSieveOperator
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m]
namespace OAI.FiniteSieveOperator
theorem _root_.solution {κ : Type*} [Fintype κ]
    (A B : Matrix m n ℂ) (c : κ → ℂ) (l : κ → m → ℂ) (r : κ → n → ℂ)
    (hl : ∀ k i, ‖l k i‖ ≤ 1) (hr : ∀ k j, ‖r k j‖ ≤ 1)
    (heq : ∀ i j, A i j = ∑ k, c k * (l k i * B i j * r k j)) :
    ‖operator A‖ ≤ (∑ k, ‖c k‖) * ‖operator B‖ := by
  let T : κ → Matrix m n ℂ := fun k i j => l k i * B i j * r k j
  have hA : A = ∑ k, c k • T k := by
    ext i j
    rw [Matrix.sum_apply]
    exact heq i j
  have hOp : operator A = ∑ k, c k • operator (T k) := by
    calc
      _ = operator (∑ k, c k • T k) := congrArg operator hA
      _ = ∑ k, operator (c k • T k) := operator_sum _ _
      _ = _ := Finset.sum_congr rfl (fun k _ => operator_smul (c k) (T k))
  rw [hOp]
  calc
    _ ≤ ∑ k, ‖c k • operator (T k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖c k‖ * ‖operator B‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (diagonal_twist_norm_le B (l k) (r k) (hl k) (hr k))
        (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm
end OAI.FiniteSieveOperator
