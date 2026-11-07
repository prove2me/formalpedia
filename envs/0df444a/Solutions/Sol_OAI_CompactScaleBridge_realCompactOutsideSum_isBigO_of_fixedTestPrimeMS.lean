-- Prove2me | solution 1 for OAI.CompactScaleBridge.realCompactOutsideSum_isBigO_of_fixedTestPrimeMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:53:36.641139+00:00
-- url     : https://prove2.me/submissions/29694e79-3c74-4b81-8971-6b40b415e661

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Theorems.Thm_OAI_CompactScaleBridge_realCompactOutsideSum_bound_of_fixedTestPrimeMS
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
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics
namespace OAI.CompactScaleBridge
theorem _root_.solution
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (LipC ε : ℝ) (m₀ : ℕ)
    (hL : 0 ≤ LipC)
    (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hε : 0 ≤ ε) (hW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (hMS : ∀ m : ℕ, m₀ ≤ m → FixedTestPrimeMS χ S hSbad W m ε) :
    (realCompactOutsideSum χ S W) =O[atTop]
      (fun D : ℝ => D ^ ((23 / 24 : ℝ) + ε)) := by
  let C : ℝ := 640 * LipC + 384 * (4 : ℝ) ^ ((23 / 24 : ℝ) + ε)
  apply isBigO_iff_isBigOWith.mpr
  refine ⟨C, IsBigOWith.of_bound ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (m₀ : ℝ))] with D hD
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hD)
  have hpow : 0 ≤ D ^ ((23 / 24 : ℝ) + ε) := Real.rpow_nonneg hDpos.le _
  have h := realCompactOutsideSum_bound_of_fixedTestPrimeMS
    χ S hSbad W LipC ε m₀ hL hLip hε hW hMS D hD
  simpa only [C, Real.norm_eq_abs, abs_of_nonneg hpow] using h
end OAI.CompactScaleBridge
