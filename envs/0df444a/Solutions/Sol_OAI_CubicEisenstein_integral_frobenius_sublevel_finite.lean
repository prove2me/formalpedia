-- Prove2me | solution 1 for OAI.CubicEisenstein.integral_frobenius_sublevel_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:35:08.264954+00:00
-- url     : https://prove2.me/submissions/585b3a7c-b09a-4de6-98f1-fd8400ecf36a

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GlobalBinLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FundamentalDomain
import Theorems.Thm_OAI_CubicEisenstein_integralRowPair_injective
import Theorems.Thm_OAI_CubicEisenstein_matrixFrobenius_integral
import Theorems.Thm_OAI_CubicEisenstein_integralRowEnergy_nonneg
import Theorems.Thm_OAI_CubicEisenstein_integralRowEnergy_sublevel_finite


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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (g : SL(2,ℂ)) (C : ℝ) :
    Set.Finite {M : SL(2,O) | matrixFrobenius (integralComplexMatrix M*g)≤C} := by
  have hs := integralRowEnergy_sublevel_finite g C
  apply (Set.Finite.preimage integralRowPair_injective.injOn (hs.prod hs)).subset
  intro M hM
  change integralRowEnergy g (integralRowPair M).1≤C ∧ integralRowEnergy g (integralRowPair M).2≤C
  change matrixFrobenius (integralComplexMatrix M*g)≤C at hM
  rw [matrixFrobenius_integral] at hM
  exact ⟨by linarith [integralRowEnergy_nonneg g (integralRowPair M).2],
    by linarith [integralRowEnergy_nonneg g (integralRowPair M).1]⟩
end OAI.CubicEisenstein
