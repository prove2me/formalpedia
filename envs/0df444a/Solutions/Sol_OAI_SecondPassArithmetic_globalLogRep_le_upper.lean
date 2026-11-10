-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalLogRep_le_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:24:25.877248+00:00
-- url     : https://prove2.me/submissions/2b8457a6-4139-4aa1-840e-e644d6472a7e

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Theorems.Thm_OAI_SecondPassArithmetic_normLogBin_mono
import Theorems.Thm_OAI_SecondPassArithmetic_normLogBin_scale_bounds


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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
namespace OAI.SecondPassArithmetic
theorem _root_.solution (caps : Fin 10 → ℝ) (j : GlobalLogIndex)
    (hj : j∈globalLogBox caps) (i : Fin 10) (Y : ℝ)
    (hc : 0<caps i) (hcap : caps i≤Y) (hY : 1≤Y) : globalLogRep j i≤Y := by
  have hji : j i≤normLogBin (caps i) := by
    have hh := Fintype.mem_piFinset.mp hj i
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  have hjY := hji.trans (normLogBin_mono hc hcap)
  have hr : globalLogRep j i≤normLogScale (normLogBin Y) := by
    unfold globalLogRep normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast hjY
  exact hr.trans (normLogBin_scale_bounds Y hY).1
end OAI.SecondPassArithmetic
