-- Prove2me | solution 1 for OAI.CompactMellinBridge.pair_zero_free_of_identity_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:54:36.391144+00:00
-- url     : https://prove2.me/submissions/ad48ecb5-c8dd-45b3-bec1-8182084bf244

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Theorems.Thm_OAI_CompactMellinBridge_zero_free_of_analytic_identity_gt_two
import Theorems.Thm_OAI_CompactMellinBridge_zero_free_of_regularized_identity_gt_two
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
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hnotboth : χ ≠ 1 ∨ ψ ≠ 1)
    (σ : ℝ) (hσ : σ < 1) (M W : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | σ < s.re})
    (heq : ∀ s : ℂ, 2 < s.re →
      (χ.LFunction s * ψ.LFunction s) * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hσtwo : σ < 2 := by linarith
  by_cases hχ : χ = 1
  · have hψ : ψ ≠ 1 := by
      intro hψ
      rcases hnotboth with h | h
      · exact h hχ
      · exact h hψ
    subst χ
    have hLregular₁ : AnalyticOnNhd ℂ
        (DirichletCharacter.LFunctionTrivChar₁ q) U :=
      (Complex.analyticOnNhd_iff_differentiableOn hopen).2
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
    have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
      (Complex.analyticOnNhd_iff_differentiableOn hopen).2
        (ψ.differentiable_LFunction hψ).differentiableOn
    have hLregular : AnalyticOnNhd ℂ
        (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) U :=
      hLregular₁.mul hLψ
    have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
        DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s =
          (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) := by
      intro s _ hs
      simp [DirichletCharacter.LFunctionTrivChar₁,
        DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
      ring
    have heqregular : ∀ s : ℂ, 2 < s.re →
        (DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) * M s =
          (s - 1) * W s := by
      intro s hs
      rw [hregular s (lt_trans hσ (by linarith : 1 < s.re)) (by
        intro h; subst s; norm_num at hs)]
      calc
        (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s =
            (s - 1) * (((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s) := by ring
        _ = (s - 1) * W s := by rw [heq s hs]
    have hprod := zero_free_of_regularized_identity_gt_two σ hσtwo
      (fun s => (1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s)
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s)
      M W hLregular hM hW hregular heqregular ρ hρ hρone hWρ
    exact mul_ne_zero_iff.mp hprod
  · by_cases hψ : ψ = 1
    · subst ψ
      have hLregular₁ : AnalyticOnNhd ℂ
          (DirichletCharacter.LFunctionTrivChar₁ r) U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (DirichletCharacter.differentiable_LFunctionTrivChar₁ r).differentiableOn
      have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (χ.differentiable_LFunction hχ).differentiableOn
      have hLregular : AnalyticOnNhd ℂ
          (fun s => χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s) U :=
        hLχ.mul hLregular₁
      have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
          χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s =
            (s - 1) * (χ.LFunction s *
              (1 : DirichletCharacter ℂ r).LFunction s) := by
        intro s _ hs
        simp [DirichletCharacter.LFunctionTrivChar₁,
          DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
        ring
      have heqregular : ∀ s : ℂ, 2 < s.re →
          (χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s) * M s =
            (s - 1) * W s := by
        intro s hs
        rw [hregular s (lt_trans hσ (by linarith : 1 < s.re)) (by
          intro h; subst s; norm_num at hs)]
        calc
          (s - 1) * (χ.LFunction s *
              (1 : DirichletCharacter ℂ r).LFunction s) * M s =
              (s - 1) * ((χ.LFunction s *
                (1 : DirichletCharacter ℂ r).LFunction s) * M s) := by ring
          _ = (s - 1) * W s := by rw [heq s hs]
      have hprod := zero_free_of_regularized_identity_gt_two σ hσtwo
        (fun s => χ.LFunction s *
          (1 : DirichletCharacter ℂ r).LFunction s)
        (fun s => χ.LFunction s * DirichletCharacter.LFunctionTrivChar₁ r s)
        M W hLregular hM hW hregular heqregular ρ hρ hρone hWρ
      exact mul_ne_zero_iff.mp hprod
    · have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (χ.differentiable_LFunction hχ).differentiableOn
      have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
        (Complex.analyticOnNhd_iff_differentiableOn hopen).2
          (ψ.differentiable_LFunction hψ).differentiableOn
      have hprod := zero_free_of_analytic_identity_gt_two σ hσtwo
        (fun s => χ.LFunction s * ψ.LFunction s) M W
        (hLχ.mul hLψ) hM hW heq ρ hρ hWρ
      exact mul_ne_zero_iff.mp hprod
end OAI.CompactMellinBridge
