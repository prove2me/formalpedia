-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_invariant_reserved_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:34:47.432456+00:00
-- url     : https://prove2.me/submissions/4ad41919-9cf4-4810-ac40-dc029aeed2be

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Theorems.Thm_OAI_InitialMeanSquare_initial_invariant_power

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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.InitialMeanSquare
namespace OAI.InitialMeanSquare
theorem _root_.solution (Z B F R c : ℝ)
    (hZ : 1≤Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) (hc : c≤Z^((1:ℝ)/20)) :
    rowScale Z (Z^((11:ℝ)/10)) B*R≤
      columnScale Z B F*F*Z^(-(1:ℝ)/20) := by
  have hZ0 : 0<Z := by linarith
  have hmass : 0<columnScale Z B F*F := by unfold columnScale; positivity
  rw [mul_comm (columnScale Z B F*F)]
  apply (div_le_iff₀ hmass).mp
  apply (initial_invariant_power Z B F R c hZ hB hF hR).trans
  calc
    c*Z^(-(1:ℝ)/10) ≤ Z^((1:ℝ)/20)*Z^(-(1:ℝ)/10) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hZ0.le _)
    _ = Z^(-(1:ℝ)/20) := by rw [←Real.rpow_add hZ0]; norm_num
end OAI.InitialMeanSquare
