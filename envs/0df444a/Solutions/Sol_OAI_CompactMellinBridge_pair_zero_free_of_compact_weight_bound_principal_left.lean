-- Prove2me | solution 1 for OAI.CompactMellinBridge.pair_zero_free_of_compact_weight_bound_principal_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:20:40.283601+00:00
-- url     : https://prove2.me/submissions/439bdfcc-cd20-42d3-b8a4-0cd3979aaf6f

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_CompactMellinBridge_normFiber_compact_euler_identity
import Theorems.Thm_OAI_CompactMellinBridge_pair_zero_free_of_weighted_identity_principal_left
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
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff
          (1 : DirichletCharacter ℂ q) ψ n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖))
    (σ : ℝ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0))
    (hzero : (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (htop : (fun D : ℝ => F D⁻¹) =O[atTop] (fun D : ℝ => D ^ σ))
    (hWanalytic : AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re})
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : mellin W ρ ≠ 0) :
    (1 : DirichletCharacter ℂ q).LFunction ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => F D⁻¹) (-s))
      {s : ℂ | σ < s.re} :=
    ShortDraftMellin.inverse_mellin_analytic _ σ hlocal htop hzero
  have heq (s : ℂ) (hs : 1 < s.re) :
      ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) *
        mellin (fun D : ℝ => F D⁻¹) (-s) = mellin W s :=
    normFiber_compact_euler_identity 1 ψ weight hcoeff hcoeff0 W F
      hF s hs (hint s hs) (hsumint s hs)
  exact pair_zero_free_of_weighted_identity_principal_left ψ hψ σ hσ
    (fun s => mellin (fun D : ℝ => F D⁻¹) (-s)) (mellin W)
    hM hWanalytic heq ρ hρ hρone hWρ
end OAI.CompactMellinBridge
