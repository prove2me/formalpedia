-- Prove2me | solution 1 for OAI.SixthPowerAverage.totient_sum_normalized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:49:07.581196+00:00
-- url     : https://prove2.me/submissions/759f7f47-d840-4caf-9e01-d250fc796998

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ThetaDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Theorems.Thm_OAI_SixthPowerAverage_idealRowSum_sixth_average


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
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
namespace OAI.SixthPowerAverage
theorem _root_.solution {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    Y*‖paperRadialFourier V 0‖*
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*totientDensity I‖≤
      ‖∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6)‖+
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖ := by
  have he:=idealRowSum_sixth_average F hF hg χ W V Y hY
  have hh:=norm_sub_le (∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6))
    (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
      maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y)
  rw [he,add_sub_cancel_right,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY] at hh
  rwa [←he] at hh
end OAI.SixthPowerAverage
