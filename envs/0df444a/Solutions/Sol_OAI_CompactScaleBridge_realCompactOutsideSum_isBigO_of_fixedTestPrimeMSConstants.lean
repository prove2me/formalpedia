-- Prove2me | solution 1 for OAI.CompactScaleBridge.realCompactOutsideSum_isBigO_of_fixedTestPrimeMSConstants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:54:48.63758+00:00
-- url     : https://prove2.me/submissions/163d8d9d-fd64-46cf-a0d1-8ee40c7351b6

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Theorems.Thm_OAI_CompactScaleBridge_realCompactOutsideSum_isBigO_of_fixedTestPrimeMS
import Theorems.Thm_OAI_ConcretePrimeRowBridge_eventually_absorb_MS_and_count_constants


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
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics
namespace OAI.CompactScaleBridge
theorem _root_.solution
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (LipC ε η Cmean Ccount : ℝ) (m₀ : ℕ)
    (hLipC : 0 ≤ LipC)
    (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hε : 0 ≤ ε) (hη : 0 < η) (hCcount : 0 < Ccount)
    (hW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (hMS : ∀ m : ℕ, m₀ ≤ m →
      FixedTestPrimeMSConstants χ S hSbad W m ε Cmean Ccount) :
    (realCompactOutsideSum χ S W) =O[atTop]
      (fun D : ℝ => D ^ ((23 / 24 : ℝ) + (ε + η))) := by
  obtain ⟨N₀, hAbsorb⟩ :=
    eventually_absorb_MS_and_count_constants Cmean Ccount η hCcount hη
  let m₁ := max 1 (max m₀ N₀)
  have hMS' : ∀ m : ℕ, m₁ ≤ m →
      FixedTestPrimeMS χ S hSbad W m (ε + η) := by
    intro m hm
    have hm₀ : m₀ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
    have hN₀ : N₀ ≤ 2 * m := by omega
    have hmPos : 0 < m := by omega
    have habs := hAbsorb (2 * m) hN₀
    exact (hMS m hm₀).absorb χ S hSbad W m ε η Cmean Ccount
      hmPos habs.1 habs.2
  exact realCompactOutsideSum_isBigO_of_fixedTestPrimeMS χ S hSbad
    W LipC (ε + η) m₁ hLipC hLip (add_nonneg hε hη.le) hW hMS'
end OAI.CompactScaleBridge
