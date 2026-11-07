-- Prove2me | solution 1 for OAI.CompactMellinBridge.baseChange_outsideCompact_zero_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:55:44.985276+00:00
-- url     : https://prove2.me/submissions/1451cc89-981d-4c52-a54c-a6a59302bb88

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Theorems.Thm_OAI_CompactMellinBridge_weighted_sum_inv_locallyIntegrableOn_pos
import Theorems.Thm_OAI_CompactMellinBridge_finiteEulerFactor_analytic
import Theorems.Thm_OAI_CompactMellinBridge_outsideCoeff_baseChange_zero
import Theorems.Thm_OAI_CompactMellinBridge_outsideCompactSum_hasSum
import Theorems.Thm_OAI_CompactMellinBridge_outside_compact_euler_identity
import Theorems.Thm_OAI_CompactMellinBridge_pair_zero_free_of_identity_gt_two
import Theorems.Thm_OAI_CompactMellinBridge_compact_weight_mellin_analytic
import Theorems.Thm_OAI_CompactMellinBridge_weighted_sum_zero_near_small_D
import Theorems.Thm_OAI_ShortDraftHeckeBridge_baseChangeChar_ne_one_of_one
import Theorems.Thm_OAI_ShortDraftMellin_inverse_mellin_analytic


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
theorem _root_.solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (hS : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (σ : ℝ)
    (htop : (fun D : ℝ => outsideCompactSum χ S W D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hσρ : σ < ρ.re) (hρone : ρ.re < 1)
    (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  let a : ℕ → ℂ := FiniteSFactor.outsideCoeff S
    (ShortDraftHeckeBridge.baseChangeWeight χ)
  have ha0 : a 0 = 0 := outsideCoeff_baseChange_zero χ S
  have hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t))
        (outsideCompactSum χ S W t) := by
    intro t ht
    exact outsideCompactSum_hasSum χ S W (fun y hy => hsupp y (Or.inr hy)) t ht
  have hlocal : LocallyIntegrableOn
      (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (Set.Ioi 0) :=
    weighted_sum_inv_locallyIntegrableOn_pos a W
      (outsideCompactSum χ S W) hW
      (fun y hy => hsupp y (Or.inr hy)) hF
  have hzero : (fun D : ℝ => outsideCompactSum χ S W D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => 0) :=
    weighted_sum_zero_near_small_D a ha0 W
      (outsideCompactSum χ S W)
      (fun y hy => hsupp y (Or.inr hy)) hF
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin
        (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (-s))
      {s : ℂ | σ < s.re} :=
    ShortDraftMellin.inverse_mellin_analytic _ σ hlocal htop hzero
  have hE : AnalyticOnNhd ℂ (finiteEulerFactor χ S)
      {s : ℂ | σ < s.re} :=
    finiteEulerFactor_analytic χ S hS σ
  have hWanalytic : AnalyticOnNhd ℂ (mellin W)
      {s : ℂ | σ < s.re} :=
    compact_weight_mellin_analytic W hW hsupp σ
  have hnotboth : χ ≠ 1 ∨ ShortDraftHeckeBridge.baseChangeChar χ ≠ 1 := by
    by_cases hχ : χ = 1
    · exact Or.inr (ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one χ hχ)
    · exact Or.inl hχ
  have heq (s : ℂ) (hs : 2 < s.re) :
      (χ.LFunction s *
        (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s) *
        (finiteEulerFactor χ S s *
          mellin (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (-s)) =
        mellin W s :=
    outside_compact_euler_identity χ S hS W hW hsupp s hs
  have hρneq : ρ ≠ 1 := by
    intro h
    subst ρ
    norm_num at hρone
  exact (pair_zero_free_of_identity_gt_two
    χ (ShortDraftHeckeBridge.baseChangeChar χ) hnotboth
    σ (lt_trans hσρ hρone)
    (fun s => finiteEulerFactor χ S s *
      mellin (fun D : ℝ => outsideCompactSum χ S W D⁻¹) (-s))
    (mellin W) (hE.mul hM) hWanalytic heq
    ρ hσρ hρneq hWρ).1
end OAI.CompactMellinBridge
