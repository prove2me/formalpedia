-- Prove2me | solution 1 for OAI.InitialMeanSquare.fiber_small_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:45:40.506691+00:00
-- url     : https://prove2.me/submissions/c4a5f286-1a0c-4ee8-a6f4-bcd0b5640967

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LiteralSources
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Theorems.Thm_OAI_InitialMeanSquare_fiber_card_le
import Theorems.Thm_OAI_IdealDivisorBound_ideal_divisor_small_power


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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
namespace OAI.InitialMeanSquare
theorem _root_.solution (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (s : Finset Datum) (y : O) (f : Ideal O), y≠0 →
      ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
        C*(Ideal.absNorm (Ideal.span {y}):ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s y f hy
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by
    intro hz
    exact hy (Ideal.span_singleton_eq_bot.mp hz)
  exact (show ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
    (idealDivisors (Ideal.span {y})).card by exact_mod_cast fiber_card_le s y f hy).trans (hdiv _ hyI)
end OAI.InitialMeanSquare
