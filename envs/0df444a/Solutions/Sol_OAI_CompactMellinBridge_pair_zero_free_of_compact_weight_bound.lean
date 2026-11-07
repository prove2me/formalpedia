-- Prove2me | solution 1 for OAI.CompactMellinBridge.pair_zero_free_of_compact_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:19:21.899103+00:00
-- url     : https://prove2.me/submissions/3089b0af-94b6-4d17-b301-d1acc9d93949

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_CompactMellinBridge_mellin_weighted_sum
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiber_LSeries_eq_pair_inverse
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pairInverseCoeff_LSeriesSummable
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_inverse_euler_identity
import Theorems.Thm_OAI_ShortDraftMellin_inverse_mellin_analytic
import Theorems.Thm_OAI_ShortDraft_zero_free_of_analytic_identity


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
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff χ ψ n)
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
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  let a : ℕ → ℂ := ShortDraftHeckeBridge.normFiberCoeff weight
  have ha0 : a 0 = 0 := hcoeff0
  have hMseries (s : ℂ) (hs : 1 < s.re) :
      mellin (fun D : ℝ => F D⁻¹) (-s) =
        mellin W s * LSeries a s := by
    apply mellin_weighted_sum a W F s ha0 (fun t ht => hF t ht)
      (hint s hs) (hsumint s hs)
    exact (LSeriesSummable_congr s (fun {n} hn => hcoeff n hn)).mpr
      (ShortDraftHeckeBridge.pairInverseCoeff_LSeriesSummable χ ψ s hs)
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hL : AnalyticOnNhd ℂ (fun s => χ.LFunction s * ψ.LFunction s) U :=
    hLχ.mul hLψ
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => F D⁻¹) (-s)) U :=
    ShortDraftMellin.inverse_mellin_analytic _ σ hlocal htop hzero
  have heq (s : ℂ) (hs : 1 < s.re) :
      (χ.LFunction s * ψ.LFunction s) *
        mellin (fun D : ℝ => F D⁻¹) (-s) = mellin W s := by
    rw [hMseries s hs,
      ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ ψ weight hcoeff s]
    have hEuler := ShortDraftHeckeBridge.pair_inverse_euler_identity χ ψ s hs
    calc
      (χ.LFunction s * ψ.LFunction s) *
          (mellin W s * LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) =
          (χ.LFunction s * ψ.LFunction s *
            LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) * mellin W s := by ring
      _ = mellin W s := by rw [hEuler]; ring
  have hprod : χ.LFunction ρ * ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_analytic_identity σ hσ
      (fun s => χ.LFunction s * ψ.LFunction s)
      (fun s => mellin (fun D : ℝ => F D⁻¹) (-s)) (mellin W)
      hL hM hWanalytic heq ρ hρ hWρ
  exact mul_ne_zero_iff.mp hprod
end OAI.CompactMellinBridge
