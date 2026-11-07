-- Prove2me | solution 1 for OAI.CompactScaleBridge.zero_free_of_fixedTestPrimeMSConstants_concrete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:50.826815+00:00
-- url     : https://prove2.me/submissions/2d4a6838-470e-4be7-9378-ac4c66fbf480

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_CompactScaleBridge_zero_free_of_fixedTestPrimeMSConstants
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_smooth
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_support
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_mellin_ne_zero
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_norm_le_one

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
open ConcreteCompactWeight
namespace OAI.CompactScaleBridge
theorem _root_.solution
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hSprime : ∀ P ∈ S, Prime P)
    (hSbad : ∀ P : Ideal ActualEisensteinCubic.O, P.IsMaximal →
      ConcretePrimeRowBridge.goodLambda ∈ P → P ∈ S)
    (ρ : ℂ)
    (ε η Cmean Ccount : ℝ) (m₀ : ℕ)
    (hε : 0 ≤ ε) (hη : 0 < η) (hCcount : 0 < Ccount)
    (hMS : ∀ m : ℕ, m₀ ≤ m →
      FixedTestPrimeMSConstants χ S hSbad (weight ρ) m ε Cmean Ccount)
    (hσρ : (23 / 24 : ℝ) + (ε + η) < ρ.re)
    (hρone : ρ.re < 1) :
    χ.LFunction ρ ≠ 0 := by
  have hρnonneg : 0 ≤ ρ.re := by linarith
  exact zero_free_of_fixedTestPrimeMSConstants
    χ S hSprime hSbad (weight ρ)
    (weight_smooth ρ) (weight_support ρ)
    (weight_norm_le_one ρ hρnonneg)
    ε η Cmean Ccount m₀ hε hη hCcount hMS
    ρ hσρ hρone (weight_mellin_ne_zero ρ)
end OAI.CompactScaleBridge
