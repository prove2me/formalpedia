-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_log_harmonic_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:37:42.038951+00:00
-- url     : https://prove2.me/submissions/9d9c062a-3fc3-476e-be3b-fc3e0f948796

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
import Theorems.Thm_OAI_InitialMeanSquare_initial_log_box_small_power
import Theorems.Thm_OAI_SecondPassArithmetic_normLogBin_le_log_upper


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
open OAI.InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)
namespace OAI.InitialMeanSquare
theorem _root_.solution :
    ∃ C : ℝ,0 < C ∧ ∀ (Y U Kmax : ℝ),1 ≤ Y → 0 < U → 0 < Kmax → U ≤ Y → Kmax ≤ Y →
      ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Y^2 := by
  obtain ⟨C,hC,hbound⟩ := initial_log_box_small_power 1 (by norm_num)
  refine ⟨C*(256*Real.exp 1),by positivity,?_⟩
  intro Y U Kmax hY hU hK hUY hKY
  have hc := hbound Y U Kmax hY hU hK hUY hKY
  rw [Real.rpow_one] at hc
  have hu := normLogBin_le_log_upper U Y hU hUY hY
  have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hY)
  have hlog : (normLogBin U : ℝ)+1 ≤ 2*Y := by linarith
  have hh : 128*Real.exp 1*(normLogBin U+1 : ℝ) ≤ (256*Real.exp 1)*Y := by
    have he := Real.exp_pos (1:ℝ)
    nlinarith
  have hnon : 0 ≤ 128*Real.exp 1*(normLogBin U+1 : ℝ) := by positivity
  calc
    _ ≤ (C*Y)*((256*Real.exp 1)*Y) := mul_le_mul hc hh hnon (by positivity)
    _ = _ := by ring
end OAI.InitialMeanSquare
