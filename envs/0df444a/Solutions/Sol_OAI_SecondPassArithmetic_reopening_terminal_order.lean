-- Prove2me | solution 1 for OAI.SecondPassArithmetic.reopening_terminal_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:35:30.522576+00:00
-- url     : https://prove2.me/submissions/87e42c2c-95a6-48ee-afda-f090aad02b16

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CutoffOrders
import Theorems.Thm_OAI_SecondPassArithmetic_exists_polynomial_cutoff_order

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
theorem _root_.solution (η R : ℝ) (hη : 0<η) :
    ∃N : ℕ,0<N ∧ ∀Z Ksrc : ℝ,1≤Z → 0≤Ksrc → Ksrc≤Z^3 →
      (Ksrc/Z^η)/Z^(η*N)≤Z^(-R) := by
  obtain ⟨N,hN,horder⟩ := exists_polynomial_cutoff_order 3 1 η R hη
  refine ⟨N,hN,?_⟩
  intro Z Ksrc hZ hK hKZ
  have hb : Ksrc/Z^η≤Z^3 := (div_le_self hK (Real.one_le_rpow hZ hη.le)).trans hKZ
  have ho : Z^3/Z^(η*N)≤Z^(-R) := by
    have hh := horder 1 Z zero_le_one hZ
    norm_num [Real.rpow_natCast] at hh ⊢
    exact hh
  exact (div_le_div_of_nonneg_right hb (by positivity)).trans ho
end OAI.SecondPassArithmetic
