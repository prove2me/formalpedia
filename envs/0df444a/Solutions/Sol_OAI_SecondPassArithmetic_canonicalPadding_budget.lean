-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalPadding_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:36:57.481015+00:00
-- url     : https://prove2.me/submissions/e0a86698-9eb3-4bd8-bb16-158dd14ca92f

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_PolynomialHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DensityBudgets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RankMargins

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
open OAI.SecondPassArithmetic
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ε C : ℝ) (hε : 0<ε) (hC : 0≤C) :
    0<canonicalPadding ε C ∧ canonicalPadding ε C≤(1:ℝ)/1000 ∧
    3000*canonicalPadding ε C≤(1:ℝ)/40 ∧
    3001*C*canonicalPadding ε C≤(1:ℝ)/40 ∧
    3001*C*canonicalPadding ε C≤ε/2 ∧
    C*canonicalPadding ε C≤(1:ℝ)/1000 := by
  let a : ℝ := min ((1:ℝ)/120040) (ε/6002)
  have ha : 0<a := lt_min (by norm_num) (div_pos hε (by norm_num))
  have ha₁ : a≤(1:ℝ)/120040 := min_le_left _ _
  have ha₂ : a≤ε/6002 := min_le_right _ _
  have hd : 0<1+C := by linarith
  have heta : 0<canonicalPadding ε C := div_pos ha hd
  have heta₁ : canonicalPadding ε C≤a := div_le_self ha.le (by linarith)
  have hCeta : C*canonicalPadding ε C≤a := by
    change C*(a/(1+C))≤a
    rw [←mul_div_assoc]
    exact (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨heta,?_,?_,?_,?_,?_⟩ <;> nlinarith
end OAI.SecondPassArithmetic
