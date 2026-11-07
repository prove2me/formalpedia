-- Prove2me | solution 1 for OAI.CompactScaleBridge.zero_free_of_fixedTestPrimeMSConstants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:58:19.84232+00:00
-- url     : https://prove2.me/submissions/831c4cbb-f235-4288-b706-0e8d7692d351

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_CompactScaleBridge_realCompactOutsideSum_eq_outsideCompactSum
import Theorems.Thm_OAI_CompactMellinBridge_baseChange_outsideCompact_zero_free
import Theorems.Thm_OAI_CompactScaleBridge_realCompactOutsideSum_isBigO_of_fixedTestPrimeMSConstants
import Theorems.Thm_OAI_CompactScaleBridge_smooth_supported_hasLipschitzConstant


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
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics
namespace OAI.CompactScaleBridge
theorem _root_.solution
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSprime : ∀ P ∈ S, Prime P)
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hSupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (hBoundW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (ε η Cmean Ccount : ℝ) (m₀ : ℕ)
    (hε : 0 ≤ ε) (hη : 0 < η) (hCcount : 0 < Ccount)
    (hMS : ∀ m : ℕ, m₀ ≤ m →
      FixedTestPrimeMSConstants χ S hSbad W m ε Cmean Ccount)
    (ρ : ℂ) (hσρ : (23 / 24 : ℝ) + (ε + η) < ρ.re)
    (hρone : ρ.re < 1) (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨LipC, hLipC, hLip⟩ :=
    smooth_supported_hasLipschitzConstant W hSmooth hSupp
  have hFinite := realCompactOutsideSum_isBigO_of_fixedTestPrimeMSConstants
    χ S hSbad W LipC ε η Cmean Ccount m₀
    hLipC hLip hε hη hCcount hBoundW hMS
  have hEq :
      (fun D : ℝ => CompactMellinBridge.outsideCompactSum χ S W D⁻¹) =ᶠ[atTop]
      (realCompactOutsideSum χ S W) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
    exact (realCompactOutsideSum_eq_outsideCompactSum χ S W D hD
      (fun y hy => hSupp y (Or.inr hy))).symm
  have hTop :
      (fun D : ℝ => CompactMellinBridge.outsideCompactSum χ S W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ ((23 / 24 : ℝ) + (ε + η))) :=
    hFinite.congr' hEq.symm Filter.EventuallyEq.rfl
  exact CompactMellinBridge.baseChange_outsideCompact_zero_free
    χ S hSprime W hSmooth hSupp ((23 / 24 : ℝ) + (ε + η)) hTop
    ρ hσρ hρone hWρ
end OAI.CompactScaleBridge
