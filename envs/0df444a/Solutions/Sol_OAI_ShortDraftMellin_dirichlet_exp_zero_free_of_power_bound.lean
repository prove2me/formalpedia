-- Prove2me | solution 1 for OAI.ShortDraftMellin.dirichlet_exp_zero_free_of_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:32:31.288088+00:00
-- url     : https://prove2.me/submissions/4f85a3bd-47e0-4647-8000-722051726a9d

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exp_mellin_identity
import Theorems.Thm_OAI_ShortDraftMellin_inverse_mellin_analytic_of_flat
import Theorems.Thm_OAI_ShortDraft_zero_free_of_analytic_identity


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
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b))
    (ρ : ℂ) (hρ : σ < ρ.re) : χ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hL : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => mobiusExpSum χ D⁻¹) (-s)) U :=
    inverse_mellin_analytic_of_flat _ σ hlocal htop hflat
  have hW : AnalyticOnNhd ℂ Complex.Gamma U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).2
    intro s hs
    apply (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    have hreal : s.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hspos : 0 < s.re := lt_trans hσpos hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hWρ : Complex.Gamma ρ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (lt_trans hσpos hρ)
  exact ShortDraft.zero_free_of_analytic_identity σ hσ χ.LFunction
    (fun s => mellin (fun D : ℝ => mobiusExpSum χ D⁻¹) (-s))
    Complex.Gamma hL hM hW
    (fun s hs => dirichlet_exp_mellin_identity χ s hs) ρ hρ hWρ
end OAI.ShortDraftMellin
