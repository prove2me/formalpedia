-- Prove2me | solution 1 for OAI.DivisorBlockCauchy.divisor_mask_energy_small_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:01:53.688241+00:00
-- url     : https://prove2.me/submissions/e41c3b32-b9d8-4b92-856a-24b76c4ebc90

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoprimeBilinearBound
import Theorems.Thm_OAI_DivisorBlockCauchy_divisor_mask_energy
import Theorems.Thm_OAI_DivisorBlockCauchy_divisorConstant_pos
import Theorems.Thm_OAI_IdealDivisorBound_ideal_divisor_small_power


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
open OAI.DivisorBlockCauchy
open IdealMobiusDivisorSum FiniteSieveOperator IdealCoprimeSieveOperator
namespace OAI.DivisorBlockCauchy
theorem _root_.solution {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O))
    (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ S, ∑ j, ‖if D ∣ column j then a j else 0‖ ^ 2) ≤
      (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  apply (divisor_mask_energy S column hcol a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2
    (column j) (hcol j)).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le) (divisorConstant_pos ε hε).le
end OAI.DivisorBlockCauchy
