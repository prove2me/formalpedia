-- Prove2me | solution 1 for OAI.ConcreteCompactWeight.weightedBump_integral_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:57:09.819552+00:00
-- url     : https://prove2.me/submissions/ada10785-43e0-4254-b4d4-f3511c470a0a

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_ConcreteCompactWeight_weightedBump_continuous
import Theorems.Thm_OAI_ConcreteCompactWeight_weightedBump_compact
import Theorems.Thm_OAI_ConcreteCompactWeight_weightedBump_nonneg
import Theorems.Thm_OAI_ConcreteCompactWeight_weightedBump_nonzero

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
theorem _root_.solution :
    0 < ∫ y : ℝ, weightedBump y := by
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    weightedBump_continuous weightedBump_compact weightedBump_nonneg
    weightedBump_nonzero
end OAI.ConcreteCompactWeight
