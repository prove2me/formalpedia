-- Prove2me | solution 1 for OAI.CompactMellinBridge.outsideCoeff_baseChange_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:45:25.615054+00:00
-- url     : https://prove2.me/submissions/8f0db58a-7649-46e8-8273-1c42b910e4eb

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution {q : ℕ}
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) :
    FiniteSFactor.outsideCoeff S
      (ShortDraftHeckeBridge.baseChangeWeight χ) 0 = 0 := by
  classical
  unfold FiniteSFactor.outsideCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 0 := by
    simpa [FiniteSFactor.fiber] using hI
  have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
  subst I
  unfold FiniteSFactor.outsideWeight
  split_ifs
  · have hz : UniqueFactorizationMonoid.moebius (⊥ : Ideal FiniteSFactor.O) = 0 := by
      simpa only [Ideal.zero_eq_bot] using
        (UniqueFactorizationMonoid.moebius_zero (α := Ideal FiniteSFactor.O))
    simp [ShortDraftHeckeBridge.baseChangeWeight, hz]
  · rfl
end OAI.CompactMellinBridge
