-- Prove2me | solution 1 for OAI.ShortDraftMellin.principal_dirichlet_exp_zero_free_of_power_bound_only
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:33:27.752701+00:00
-- url     : https://prove2.me/submissions/6f539992-1c67-4b53-bfac-8c44b9734aee

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_inv_locallyIntegrableOn_pos
import Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exp_mellin_identity
import Theorems.Thm_OAI_ShortDraftMellin_inverse_mellin_analytic_of_flat
import Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_flat_at_zero
import Theorems.Thm_OAI_ShortDraft_zero_free_of_regularized_analytic_identity


set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin
namespace OAI.ShortDraftMellin
theorem _root_.solution
    (q : ℕ) [NeZero q]
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => mobiusExpSum
        (1 : DirichletCharacter ℂ q) D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 := by
  let U : Set ℂ := {s | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLregular : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunctionTrivChar₁ q) U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin
        (fun D : ℝ => mobiusExpSum (1 : DirichletCharacter ℂ q) D⁻¹) (-s)) U :=
    inverse_mellin_analytic_of_flat _ σ
      (mobiusExpSum_inv_locallyIntegrableOn_pos 1) htop
      (mobiusExpSum_flat_at_zero 1)
  have hW : AnalyticOnNhd ℂ Complex.Gamma U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).2
    intro s hs
    apply (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    have hreal : s.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hspos : 0 < s.re := lt_trans hσpos hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      DirichletCharacter.LFunctionTrivChar₁ q s =
        (s - 1) * DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) s := by
    intro s _ hs
    simp [DirichletCharacter.LFunctionTrivChar₁,
      DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
  have heq : ∀ s : ℂ, 1 < s.re →
      DirichletCharacter.LFunctionTrivChar₁ q s *
        mellin (fun D : ℝ => mobiusExpSum
          (1 : DirichletCharacter ℂ q) D⁻¹) (-s) =
        (s - 1) * Complex.Gamma s := by
    intro s hs
    rw [hregular s (lt_trans hσ hs) (by
      intro h; subst s; norm_num at hs)]
    rw [mul_assoc, dirichlet_exp_mellin_identity 1 s hs]
  have hWρ : Complex.Gamma ρ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (lt_trans hσpos hρ)
  exact ShortDraft.zero_free_of_regularized_analytic_identity σ hσ
    (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
    (DirichletCharacter.LFunctionTrivChar₁ q)
    (fun s => mellin (fun D : ℝ => mobiusExpSum
      (1 : DirichletCharacter ℂ q) D⁻¹) (-s))
    Complex.Gamma hLregular hM hW hregular heq ρ hρ hρone hWρ
end OAI.ShortDraftMellin
