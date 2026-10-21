-- Prove2me | solution 1 for LeveragedPayouts.Unregulated.effort_labor_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:52:47.385097+00:00
-- url     : https://prove2.me/submissions/4c9aa794-77cd-47dd-b2a6-476a38417702

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

theorem solution (E : Economy) :
    StrictMonoOn (effort E) (Set.Ioc 0 E.R) ∧
    (∀ r, E.R ≤ r → effort E r = E.π) ∧
    ∀ r r' l l', 0 < r → r < r' → IsLaborDemand E r l → IsLaborDemand E r' l' → l' < l := by
  have hR : 0 < E.R := by linarith [E.hR]
  have hπ := E.hπ0
  refine ⟨?_, ?_, ?_⟩
  · intro r hr r' hr' hrr'
    simp only [Set.mem_Ioc] at hr hr'
    unfold effort
    rw [min_eq_left hr.2, min_eq_left hr'.2]
    exact div_lt_div_of_pos_left (mul_pos hπ hR) (by linarith [hr'.2]) (by linarith)
  · intro r hr
    unfold effort
    rw [min_eq_right hr]
    have : 2 * E.R - E.R = E.R := by ring
    rw [this]
    field_simp
  · have aux : ∀ r r' : ℝ, 0 < r → r < r' →
        (2 * E.R - min r E.R) * r < (2 * E.R - min r' E.R) * r' := by
      intro r r' hr hrr'
      rcases le_or_gt r' E.R with h1 | h1
      · rw [min_eq_left (hrr'.le.trans h1), min_eq_left h1]
        nlinarith [mul_pos (sub_pos.2 hrr') (show 0 < 2 * E.R - r - r' by linarith)]
      · rcases le_or_gt r E.R with h2 | h2
        · rw [min_eq_left h2, min_eq_right h1.le]
          nlinarith [sq_nonneg (E.R - r), mul_pos hR (sub_pos.2 h1)]
        · rw [min_eq_right h2.le, min_eq_right h1.le]
          nlinarith
    have hd : ∀ r l, IsLaborDemand E r l →
        E.π * E.R * deriv E.f l = r * E.wstar * (2 * (2 * E.R - min r E.R)) := by
      intro r l h
      obtain ⟨_, _, h⟩ := h
      have : 0 < 2 * (2 * E.R - min r E.R) := by
        have := min_le_right r E.R; linarith
      rw [div_eq_iff this.ne'] at h
      exact h
    intro r r' l l' hr hrr' hl hl'
    by_contra hcon
    push_neg at hcon
    have h1 : deriv E.f l' ≤ deriv E.f l := by
      rcases hcon.lt_or_eq with h | h
      · exact (fprime_strictAnti E hl.1 hl'.1 h).le
      · rw [h]
    have h2 := hd r l hl
    have h3 := hd r' l' hl'
    have hw := wstar_pos E
    have h4 := mul_lt_mul_of_pos_left (aux r r' hr hrr') hw
    have h5 : E.π * E.R * deriv E.f l' ≤ E.π * E.R * deriv E.f l :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [h2, h3] at h5
    nlinarith
