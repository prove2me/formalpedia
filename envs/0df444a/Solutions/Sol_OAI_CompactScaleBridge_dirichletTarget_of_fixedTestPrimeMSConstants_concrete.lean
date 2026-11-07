-- Prove2me | solution 1 for OAI.CompactScaleBridge.dirichletTarget_of_fixedTestPrimeMSConstants_concrete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:01:15.070077+00:00
-- url     : https://prove2.me/submissions/bbbfb152-dd44-4488-a2ea-e73be0b97f04

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_CompactScaleBridge_zero_free_of_fixedTestPrimeMSConstants_concrete
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
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.CompactScaleBridge
namespace OAI.CompactScaleBridge
theorem _root_.solution
    (hMS : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
      ∃ S : Finset (Ideal ActualEisensteinCubic.O),
      ∃ _hSprime : ∀ P ∈ S, Prime P,
      ∃ hSbad : ∀ P : Ideal ActualEisensteinCubic.O,
        P.IsMaximal → ConcretePrimeRowBridge.goodLambda ∈ P → P ∈ S,
      ∃ ε η Cmean Ccount : ℝ, ∃ m₀ : ℕ,
      ∃ _hmean : ∀ m : ℕ, m₀ ≤ m →
          FixedTestPrimeMSConstants χ S hSbad
            (ConcreteCompactWeight.weight ρ) m ε Cmean Ccount,
        0 ≤ ε ∧ 0 < η ∧ 0 < Ccount ∧
        (23 / 24 : ℝ) + (ε + η) < ρ.re) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρone : ρ.re < 1
  · obtain ⟨S, hSprime, hSbad, ε, η, Cmean, Ccount, m₀,
      hmean, hε, hη, hCcount, hgap⟩ := hMS q χ ρ h23 hρone
    exact zero_free_of_fixedTestPrimeMSConstants_concrete
      χ S hSprime hSbad ρ ε η Cmean Ccount m₀
      hε hη hCcount hmean hgap hρone
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρone) hprincipal
end OAI.CompactScaleBridge
