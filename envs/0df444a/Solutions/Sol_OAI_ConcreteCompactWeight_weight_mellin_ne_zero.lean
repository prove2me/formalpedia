-- Prove2me | solution 1 for OAI.ConcreteCompactWeight.weight_mellin_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:58:41.051722+00:00
-- url     : https://prove2.me/submissions/a5053ddd-5ae1-4842-9934-69710cbb17c4

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_mellin_eq_bump
import Theorems.Thm_OAI_ConcreteCompactWeight_weightedBump_integral_pos
import Theorems.Thm_OAI_ConcreteCompactWeight_mellin_bump_zero_eq_integral_weightedBump

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
open OAI.ConcreteCompactWeight
namespace OAI.ConcreteCompactWeight
theorem _root_.solution (ρ : ℂ) : mellin (weight ρ) ρ ≠ 0 := by
  rw [weight_mellin_eq_bump, mellin_bump_zero_eq_integral_weightedBump]
  exact Complex.ofReal_ne_zero.mpr weightedBump_integral_pos.ne'
end OAI.ConcreteCompactWeight
