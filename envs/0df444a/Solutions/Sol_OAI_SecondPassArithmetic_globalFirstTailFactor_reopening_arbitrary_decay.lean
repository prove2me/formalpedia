-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstTailFactor_reopening_arbitrary_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:43:22.354783+00:00
-- url     : https://prove2.me/submissions/b6f1811b-5b58-4309-bbd8-0d4d0d041cbb

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningBounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstTailFactor_reopening_power

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
theorem _root_.solution (A M κ R : ℝ) (hκ : 0<κ) :
    ∃N : ℕ,0<N ∧ ∀Z η X F Ksrc B : ℝ,
      1≤Z → 0≤η → 1≤X → X≤Z^3 → 1≤F → F≤Z^3 →
      1≤Ksrc → Ksrc≤Z^3 → 1≤B → B^3≤Real.exp A*X →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
        (reopeningAuxiliaryScale A M κ Z) (Z^κ) N ≤
        (4096*(reopeningScaleConstant A M)^20)*Z^(-R) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((20*(κ+3)+R)/κ))
  have hN0 : 0<N := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  have hNR : (20*(κ+3)+R)/κ<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hexp : 20*(κ+3)-κ*(N:ℝ)≤-R := by
    have hm := (div_lt_iff₀ hκ).mp hNR
    nlinarith
  refine ⟨N,hN0,?_⟩
  intro Z η X F Ksrc B hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  exact (globalFirstTailFactor_reopening_power A M κ Z η X F Ksrc B N hκ.le hZ hη
    hX hXZ hF hFZ hK hKZ hB hactive).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity))
end OAI.SecondPassArithmetic
