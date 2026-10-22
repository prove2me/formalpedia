-- Prove2me | solution 1 for NonlinSSD.DualFunctional.exists_maximizer_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:05:02.36736+00:00
-- url     : https://prove2.me/submissions/5e5ac1a3-ca7b-4302-a3ca-b6bf7fe776f5

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Basic

set_option autoImplicit false
open MeasureTheory NonlinSSD.DualFunctional

theorem solution (a b : ℝ) (hab : a ≤ b) (v : ℝ → ℝ) (hv : v ∈ NonlinSSD.Optimality.U1 a b)
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξc : ξ ≤ leftDeriv v a) :
    ∃ t₀ ∈ Set.Icc a b, (∀ t : ℝ, v t - ξ * t ≤ v t₀ - ξ * t₀) ∧
      concaveConj v ξ = ((ξ * t₀ - v t₀ : ℝ) : EReal) := by
  obtain ⟨hconc, hmono, hb, c, hc0, hlin⟩ := hv
  have hld : leftDeriv v a = c := by
    unfold leftDeriv
    have h1 : HasDerivWithinAt (fun t : ℝ => v a + c * (t - a)) c (Set.Iic a) a := by
      have : HasDerivAt (fun t : ℝ => v a + c * (t - a)) c a := by
        simpa using (((hasDerivAt_id a).sub_const a).const_mul c).const_add (v a)
      exact this.hasDerivWithinAt
    have h2 : HasDerivWithinAt v c (Set.Iic a) a :=
      h1.congr (fun x hx => hlin x hx) (by simp)
    exact h2.derivWithin (uniqueDiffWithinAt_Iic a)
  rw [hld] at hξc
  have hcont : Continuous v := by
    have := hconc.continuousOn isOpen_univ
    rwa [continuousOn_univ] at this
  have hg : Continuous (fun t => v t - ξ * t) := hcont.sub (continuous_const.mul continuous_id)
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab) hg.continuousOn
  have hall : ∀ t, v t - ξ * t ≤ v t0 - ξ * t0 := by
    intro t
    rcases le_or_gt t a with h | h
    · have e1 := hlin t h
      have e2 := hmax (Set.mem_Icc.2 ⟨le_refl a, hab⟩)
      have e3 : v a - ξ * a ≤ v t0 - ξ * t0 := e2
      nlinarith [mul_nonneg (sub_nonneg.2 hξc) (sub_nonneg.2 h)]
    rcases le_or_gt b t with h' | h'
    · have e1 := hb t h'
      have e1' := hb b (le_refl b)
      have e2 := hmax (Set.mem_Icc.2 ⟨hab, le_refl b⟩)
      have e3 : v b - ξ * b ≤ v t0 - ξ * t0 := e2
      nlinarith
    · exact hmax (Set.mem_Icc.2 ⟨h.le, h'.le⟩)
  refine ⟨t0, ht0, hall, ?_⟩
  unfold concaveConj
  apply le_antisymm
  · exact iInf_le (fun t => ((ξ * t - v t : ℝ) : EReal)) t0
  · refine le_iInf (fun t => ?_)
    exact_mod_cast (by linarith [hall t] : ξ * t0 - v t0 ≤ ξ * t - v t)
