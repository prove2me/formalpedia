-- Prove2me | solution 1 for OAI.CompactMellinBridge.dirichletTarget_of_compact_outside_tests
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:29.525198+00:00
-- url     : https://prove2.me/submissions/fce35de3-7bfb-4f91-b1a8-29ee60db6a0b

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Theorems.Thm_OAI_CompactMellinBridge_baseChange_outsideCompact_zero_free
import Theorems.Thm_OAI_ShortDraft_dirichlet_target_of_one_le_re


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
theorem _root_.solution
    (hTest : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        BaseChangeOutsideCompactTest χ ρ) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · let T := hTest q χ ρ h23 hρ
    exact baseChange_outsideCompact_zero_free χ T.S T.S_prime
      T.W T.smooth T.support T.sigma T.power_bound
      ρ T.sigma_lt hρ T.mellin_nonzero
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal
end OAI.CompactMellinBridge
