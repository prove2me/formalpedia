-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstTailFactor_reopening_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:48:37.388199+00:00
-- url     : https://prove2.me/submissions/47f3e277-fc44-4786-8760-ac9aee5f6529

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningBounds
import Theorems.Thm_OAI_SecondPassArithmetic_reopeningAuxiliaryScale_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstTailFactor_envelope

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
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
namespace OAI.SecondPassArithmetic
theorem _root_.solution (A M κ Z η X F Ksrc B : ℝ) (N : ℕ)
    (hκ : 0≤κ) (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (reopeningAuxiliaryScale A M κ Z) (Z^κ) N ≤
      (4096*(reopeningScaleConstant A M)^20)*Z^(20*(κ+3)-κ*N) := by
  have hZ0 : 0<Z := by linarith
  have hB0 : 0<B := by linarith
  have hX0 : 0<X := by linarith
  have hs := reopeningAuxiliaryScale_bounds A M κ Z η X F Ksrc B hκ hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  have hBsup : 1≤Real.exp 1*B := one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hbound := globalFirstTailFactor_envelope (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
    (reopeningAuxiliaryScale A M κ Z) (Z^κ) N (by positivity) (by positivity) hBsup hF hs.1
    (by positivity) hs.2.1 hs.2.2.2.2.2.2.2.2
  apply hbound.trans
  have hden : (Z^κ)^N≤(1+Z^κ)^N := pow_le_pow_left₀ (by positivity) (by linarith [Real.rpow_pos_of_pos hZ0 κ]) N
  calc
    _ ≤ 4096*(reopeningAuxiliaryScale A M κ Z)^20/(Z^κ)^N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      unfold reopeningAuxiliaryScale
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_mul_natCast hZ0.le,
        Real.rpow_sub hZ0]
      ring_nf
end OAI.SecondPassArithmetic
