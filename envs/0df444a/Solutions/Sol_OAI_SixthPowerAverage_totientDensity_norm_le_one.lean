-- Prove2me | solution 1 for OAI.SixthPowerAverage.totientDensity_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:40:25.096483+00:00
-- url     : https://prove2.me/submissions/c1247f00-ffe1-4013-8ecd-7d958f5a517b

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ThetaDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Theorems.Thm_OAI_IdealDivisorBound_support_norm_two_le


set_option autoImplicit false
open OAI
noncomputable section
open OAI.SixthPowerAverage
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
open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open IdealMobiusDivisorSum hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion
open InitialMeanSquare
namespace OAI.SixthPowerAverage
theorem _root_.solution (I : Ideal ActualEisensteinCubic.O) : ‖totientDensity I‖≤1 := by
  rw [totientDensity,norm_prod]
  apply Finset.prod_le_one
  · intro P hP
    exact norm_nonneg _
  · intro P hP
    have hN : (2:ℝ)≤Ideal.absNorm P:=by exact_mod_cast IdealDivisorBound.support_norm_two_le hP
    have hNp : (0:ℝ)<Ideal.absNorm P:=by linarith
    have he : (1-(1:ℂ)/(Ideal.absNorm P:ℂ))=((1-1/(Ideal.absNorm P:ℝ):ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    · exact sub_le_self _ (by positivity)
    · have hi : (1:ℝ)/(Ideal.absNorm P:ℝ)≤1 := (div_le_one hNp).mpr (by linarith)
      linarith
end OAI.SixthPowerAverage
