-- Prove2me | solution 1 for OAI.DescentFiberCost.finite_ideal_count_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:07:25.224784+00:00
-- url     : https://prove2.me/submissions/a20f480f-ba66-497c-9303-336d1e64dc63

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_InverseContour
import Theorems.Thm_OAI_CompactScaleBridge_idealsUpTo_card_le


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
open OAI.DescentFiberCost
open scoped BigOperators Classical
open ConcretePrimeRowBridge
namespace OAI.DescentFiberCost
theorem _root_.solution (s : Finset (Ideal O)) (H : ℝ) (hH : 1 ≤ H)
    (hpos : ∀ I ∈ s, I ≠ ⊥) (hN : ∀ I ∈ s, (Ideal.absNorm I : ℝ) ≤ H) :
    (s.card : ℝ) ≤ 128 * H := by
  have hs : s ⊆ idealsUpTo ⌊H⌋₊ := by
    intro I hI
    apply mem_idealsUpTo.mpr
    refine ⟨?_, Nat.le_floor (hN I hI)⟩
    exact Nat.one_le_iff_ne_zero.mpr (fun h => hpos I hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hc := (Finset.card_le_card hs).trans (CompactScaleBridge.idealsUpTo_card_le ⌊H⌋₊)
  have hfloor : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hr : (s.card : ℝ) ≤ 64 * ((⌊H⌋₊ : ℝ) + 1) := by exact_mod_cast hc
  linarith
end OAI.DescentFiberCost
