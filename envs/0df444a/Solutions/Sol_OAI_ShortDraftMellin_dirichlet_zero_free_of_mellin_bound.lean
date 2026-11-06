-- Prove2me | solution 1 for OAI.ShortDraftMellin.dirichlet_zero_free_of_mellin_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:23.950079+00:00
-- url     : https://prove2.me/submissions/0f0e796c-9a30-4a3c-b87e-f8e8b0536c6f

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Theorems.Thm_OAI_ShortDraftMellin_inverse_mellin_analytic

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
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (σ : ℝ) (hσ : σ < 1)
    (A : ℝ → ℂ) (W : ℂ → ℂ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (hW : Differentiable ℂ W)
    (heq : ∀ s : ℂ, 1 < s.re →
      χ.LFunction s * mellin A (-s) = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hL : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hM : AnalyticOnNhd ℂ (fun s : ℂ => mellin A (-s)) U :=
    inverse_mellin_analytic A σ hlocal htop hzero
  have hWa : AnalyticOnNhd ℂ W U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2 hW.differentiableOn
  have htwo : (2 : ℂ) ∈ U := by
    change σ < (2 : ℂ).re
    norm_num at *
    linarith
  have heventual : (fun s : ℂ => χ.LFunction s * mellin A (-s)) =ᶠ[𝓝 (2 : ℂ)] W := by
    filter_upwards [((Complex.isOpen_re_gt 1).mem_nhds (by norm_num :
      (2 : ℂ) ∈ {s : ℂ | 1 < s.re}))] with s hs
    exact heq s hs
  have hid : Set.EqOn (fun s : ℂ => χ.LFunction s * mellin A (-s)) W U :=
    (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hWa
      ((convex_halfSpace_re_gt σ).isPreconnected) htwo heventual
  intro hzeroL
  have heqρ := hid hρ
  change χ.LFunction ρ * mellin A (-ρ) = W ρ at heqρ
  rw [hzeroL, zero_mul] at heqρ
  exact hWρ heqρ.symm
end OAI.ShortDraftMellin
