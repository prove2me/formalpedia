-- Prove2me | solution 1 for OAI.LocalLogFourier.momentConstant_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:58:54.506089+00:00
-- url     : https://prove2.me/submissions/351b0afd-760e-4d54-8bf9-0d02003771e9

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_derivativeConstant_nonneg

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
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
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
open OAI.LocalLogFourier
namespace OAI.LocalLogFourier
theorem _root_.solution (K n : ℕ) (Lwin CW CF : ℝ)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K) :
    (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
      derivativeConstant n CW CF ≤ momentConstant K Lwin CW CF := by
  unfold momentConstant
  apply Finset.single_le_sum
    (f := fun i : ℕ =>
      (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
        derivativeConstant i CW CF)
    (a := n)
  · intro i hi
    exact mul_nonneg (by positivity)
      (derivativeConstant_nonneg i CW CF hCW hCF)
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
end OAI.LocalLogFourier
