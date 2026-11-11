-- Prove2me | solution 1 for OAI.CompletedHeight.shortCompletedSum_normHeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:15:52.511026+00:00
-- url     : https://prove2.me/submissions/375dc3ac-4e7a-4d35-aac1-f21ebe68849b

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_PolynomialHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PolynomialHeight
import Theorems.Thm_OAI_CompletedHeight_cubeWeight_normHeight
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight
import Theorems.Thm_OAI_CompletedGauss_mem_shortCubeRange
import Theorems.Thm_OAI_CompletedGauss_norm_at_least_one
import Theorems.Thm_OAI_CompletedGauss_shortCompletedSum_eq
import Theorems.Thm_OAI_FourierBridge_logPhase_add


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CompletedHeight
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
open scoped BigOperators Classical
open CompletedGauss hiding O
open ActualEisensteinCubic
open SecondPassArithmetic (normPhase normHeightTwist)
open FourierBridge (logPhase)
namespace OAI.CompletedHeight
theorem _root_.solution (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X H₀ : ℝ) (hX : 0<X) :
    shortCompletedSum (normHeightTwist Ψ t) W X H₀ =
      logPhase t (Real.log X)*shortCompletedSum Ψ (normTwistedSource W t) X H₀ := by
  rw [shortCompletedSum_eq,shortCompletedSum_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  have hn : 0<(Ideal.absNorm H:ℝ) := lt_of_lt_of_le zero_lt_one
    (norm_at_least_one H ((mem_shortCubeRange H₀ H).mp hH).1)
  rw [cubeWeight_normHeight,completedT_normHeight Ψ W t _ (div_pos hX (pow_pos hn 3))]
  have hl : 3*Real.log (Ideal.absNorm H:ℝ)+Real.log (X/(Ideal.absNorm H:ℝ)^3)=Real.log X := by
    rw [Real.log_div hX.ne' (pow_pos hn 3).ne',Real.log_pow]
    push_cast
    ring
  have hphase : logPhase t (3*Real.log (Ideal.absNorm H:ℝ))*
      logPhase t (Real.log (X/(Ideal.absNorm H:ℝ)^3))=logPhase t (Real.log X) := by
    rw [←FourierBridge.logPhase_add,hl]
  linear_combination (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    completedT Ψ (normTwistedSource W t) (X/(Ideal.absNorm H:ℝ)^3)*hphase
end OAI.CompletedHeight
