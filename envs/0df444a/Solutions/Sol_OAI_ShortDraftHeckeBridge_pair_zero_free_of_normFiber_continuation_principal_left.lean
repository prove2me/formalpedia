-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.pair_zero_free_of_normFiber_continuation_principal_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:47:04.347741+00:00
-- url     : https://prove2.me/submissions/6eb7f66f-5ce5-4ceb-ba2a-fa7d664344ed

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiber_LSeries_eq_pair_inverse
import Theorems.Thm_OAI_ShortDraftHeckeBridge_pair_inverse_euler_identity
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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff (1 : DirichletCharacter ℂ q) ψ n)
    (σ : ℝ) (hσ : σ < 1) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hMseries : ∀ s : ℂ, 1 < s.re → M s = LSeries (normFiberCoeff weight) s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 ∧
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
  have hW : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) U := analyticOnNhd_const
  have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s =
        (s - 1) *
          (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
            ψ.LFunction s) := by
    intro s _ hs
    simp [DirichletCharacter.LFunctionTrivChar₁,
      DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
    ring
  have heq : ∀ s : ℂ, 1 < s.re →
      (DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) * M s =
        (s - 1) * 1 := by
    intro s hs
    rw [hregular s (lt_trans hσ hs) (by
      intro h; subst s; norm_num at hs)]
    rw [hMseries s hs, normFiber_LSeries_eq_pair_inverse 1 ψ weight hcoeff s]
    calc
      (s - 1) * (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
          ψ.LFunction s) * LSeries (pairInverseCoeff 1 ψ) s =
        (s - 1) * (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
          ψ.LFunction s * LSeries (pairInverseCoeff 1 ψ) s) := by ring
      _ = (s - 1) * 1 := by rw [pair_inverse_euler_identity 1 ψ s hs]
  have hprod :
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ *
        ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_regularized_analytic_identity σ hσ
      (fun s => DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
        ψ.LFunction s)
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s)
      M (fun _ => (1 : ℂ)) hLregular hM hW hregular heq ρ hρ hρone
      one_ne_zero
  exact mul_ne_zero_iff.mp hprod
end OAI.ShortDraftHeckeBridge
