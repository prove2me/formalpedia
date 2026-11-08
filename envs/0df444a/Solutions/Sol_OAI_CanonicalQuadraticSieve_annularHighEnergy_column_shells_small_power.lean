-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.annularHighEnergy_column_shells_small_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:07:37.865767+00:00
-- url     : https://prove2.me/submissions/95208541-f240-440a-a640-75764eeae5cf

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DyadicColumns
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnDyadicLength_small_power
import Theorems.Thm_OAI_CanonicalQuadraticSieve_annularHighEnergy_column_shells_at_scale


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
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    (ε : ℝ) (hε : 0 < ε) (M N K : ℝ) (hN : 1 ≤ N) (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ ((2 + 1 / (ε * Real.log 2)) * N ^ ε) *
      ∑ j : Fin (columnDyadicLength N + 1),
        annularHighEnergy M ((2 : ℝ) ^ j.val) K
          (coefficientAtScale N ((2 : ℝ) ^ j.val)
            (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)) := by
  apply (annularHighEnergy_column_shells_at_scale M N K (columnDyadicLength N)
    (columnDyadicLength_cover N) a).trans
  apply mul_le_mul_of_nonneg_right (columnDyadicLength_small_power ε hε N hN)
  apply Finset.sum_nonneg
  intro j _
  unfold annularHighEnergy
  exact Finset.sum_nonneg (fun I _ => mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (sq_nonneg _))
end OAI.CanonicalQuadraticSieve
