-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.eventually_absorb_MS_and_count_constants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:20:12.930509+00:00
-- url     : https://prove2.me/submissions/f51397f2-6ad4-42da-b511-e717b520b10b

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
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
open OAI.ConcretePrimeRowBridge
open ShortDraftHeckeBridge FiniteSFactor
open ShortDraftHeckeBridge FiniteSFactor Filter
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (Cmean Ccount eta : ℝ) (hcount : 0 < Ccount) (heta : 0 < eta) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      Cmean ≤ (D : ℝ) ^ eta ∧ 1 ≤ Ccount * (D : ℝ) ^ eta := by
  have hpow : Tendsto (fun D : ℕ => (D : ℝ) ^ eta) atTop atTop :=
    (tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp
    (hpow.eventually_ge_atTop (max Cmean Ccount⁻¹))
  refine ⟨D₀, fun D hD => ?_⟩
  have hlarge := hD₀ D hD
  constructor
  · exact (le_max_left _ _).trans hlarge
  · have hinv : Ccount⁻¹ ≤ (D : ℝ) ^ eta :=
      (le_max_right _ _).trans hlarge
    have hmul := mul_le_mul_of_nonneg_left hinv hcount.le
    simpa [hcount.ne'] using hmul
end OAI.ConcretePrimeRowBridge
