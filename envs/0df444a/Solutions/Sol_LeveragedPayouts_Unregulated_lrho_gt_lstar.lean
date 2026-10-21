-- Prove2me | solution 1 for LeveragedPayouts.Unregulated.lrho_gt_lstar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:52:45.159995+00:00
-- url     : https://prove2.me/submissions/91b595f9-939a-41a2-9279-085f3eb65ffd

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

set_option autoImplicit false
open Filter Topology LeveragedPayouts.Unregulated

theorem fprime_strictAnti (E : Economy) : StrictAntiOn (deriv E.f) (Set.Ioi 0) := by
  have hc : ContinuousOn (deriv E.f) (Set.Ioi 0) :=
    (E.hf.2.2.1).continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0) hc
  intro x hx
  rw [interior_Ioi] at hx
  exact E.hf.2.2.2.2.1 x hx

theorem wstar_pos (E : Economy) : 0 < E.wstar := by
  rw [← E.hw]
  exact E.hg.2.2.2.1 _ (by linarith [E.hl1])

theorem solution (E : Economy) (ρ lρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlρ : IsFirstBestLabor E ρ lρ) :
    E.lstar < lρ ∧ ρ * deriv E.g (1 - lρ) < E.wstar := by
  obtain ⟨hl0, hl1, heq⟩ := hlρ
  have hgpos : 0 < deriv E.g (1 - lρ) := E.hg.2.2.2.1 _ (by linarith)
  have hRpos : 0 < E.R := by linarith [E.hR]
  have hlt : E.lstar < lρ := by
    by_contra hcon
    push_neg at hcon
    have h1 : deriv E.f E.lstar ≤ deriv E.f lρ := by
      rcases hcon.lt_or_eq with h | h
      · exact (fprime_strictAnti E hl0 E.hl0 h).le
      · rw [h]
    have h2 : deriv E.g (1 - lρ) ≤ deriv E.g (1 - E.lstar) := by
      rcases hcon.lt_or_eq with h | h
      · exact (E.hg.2.2.2.2.1 (show 1 - E.lstar ∈ Set.Ioi (0:ℝ) by simp only [Set.mem_Ioi]; linarith [E.hl1])
          (show 1 - lρ ∈ Set.Ioi (0:ℝ) by simp only [Set.mem_Ioi]; linarith)
          (by linarith)).le
      · rw [h]
    have h3 : E.π / (2 * E.R) * deriv E.f E.lstar ≤ E.π / (2 * E.R) * deriv E.f lρ :=
      mul_le_mul_of_nonneg_left h1 (by have := E.hπ0; positivity)
    have h4 : E.π / (2 * E.R) * deriv E.f lρ = ρ * deriv E.g (1 - lρ) := by
      rw [← heq]; ring
    rw [E.h20] at h3
    nlinarith
  refine ⟨hlt, ?_⟩
  have h1 : deriv E.f lρ < deriv E.f E.lstar := fprime_strictAnti E E.hl0 hl0 hlt
  have h3 : E.π / (2 * E.R) * deriv E.f lρ < E.π / (2 * E.R) * deriv E.f E.lstar :=
    mul_lt_mul_of_pos_left h1 (by have := E.hπ0; positivity)
  have h4 : E.π / (2 * E.R) * deriv E.f lρ = ρ * deriv E.g (1 - lρ) := by
    rw [← heq]; ring
  rw [E.h20] at h3
  rw [← E.hw]
  linarith
