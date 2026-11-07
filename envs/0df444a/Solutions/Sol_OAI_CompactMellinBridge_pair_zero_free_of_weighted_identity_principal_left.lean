-- Prove2me | solution 1 for OAI.CompactMellinBridge.pair_zero_free_of_weighted_identity_principal_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:18:43.513241+00:00
-- url     : https://prove2.me/submissions/373f9de2-8491-46a0-90ac-f0d5f44b29be

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraft_zero_free_of_regularized_analytic_identity
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
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (σ : ℝ) (hσ : σ < 1) (M W : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | σ < s.re})
    (heq : ∀ s : ℂ, 1 < s.re →
      ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) (hWρ : W ρ ≠ 0) :
    (1 : DirichletCharacter ℂ q).LFunction ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
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
  have heqregular : ∀ s : ℂ, 1 < s.re →
      (DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) * M s =
        (s - 1) * W s := by
    intro s hs
    rw [hregular s (lt_trans hσ hs) (by
      intro h; subst s; norm_num at hs)]
    calc
      (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s =
          (s - 1) * (((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s) := by ring
      _ = (s - 1) * W s := by rw [heq s hs]
  have hprod :
      (1 : DirichletCharacter ℂ q).LFunction ρ * ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_regularized_analytic_identity σ hσ
      (fun s => (1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s)
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s)
      M W hLregular hM hW hregular heqregular ρ hρ hρone hWρ
  exact mul_ne_zero_iff.mp hprod
end OAI.CompactMellinBridge
