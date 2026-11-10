-- Prove2me | solution 1 for OAI.CompletedGauss.completedRowDyadic_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:38:53.633878+00:00
-- url     : https://prove2.me/submissions/b4a03e0f-06ac-4a69-99b0-3047c56c86cf

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Theorems.Thm_OAI_CompletedGauss_completedRowDyadic_top

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic
namespace OAI.CompletedGauss
theorem _root_.solution (K : ℝ) (hK : 1≤K) :
    (∑j∈Finset.range (completedRowDyadicLength K+1),(2:ℝ)^j)≤4*K ∧
    (∑j∈Finset.range (completedRowDyadicLength K+1),((2:ℝ)^j)^2)≤16*K^2 := by
  have ht := completedRowDyadic_top K hK
  constructor
  · rw [geom_sum_eq (by norm_num : (2:ℝ)≠1),pow_succ]
    norm_num
    linarith
  · have he (j : ℕ) : ((2:ℝ)^j)^2=(4:ℝ)^j := by rw [←pow_mul,Nat.mul_comm j 2,pow_mul]; norm_num
    simp_rw [he]
    rw [geom_sum_eq (by norm_num : (4:ℝ)≠1),pow_succ,←he]
    norm_num
    have hp := pow_le_pow_left₀ (by positivity : 0≤(2:ℝ)^(completedRowDyadicLength K)) ht 2
    nlinarith
end OAI.CompletedGauss
