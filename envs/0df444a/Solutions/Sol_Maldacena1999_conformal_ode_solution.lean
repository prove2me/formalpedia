-- Prove2me | solution 1 for Maldacena1999.conformal_ode_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T15:00:53.241885+00:00
-- url     : https://prove2.me/submissions/3f3fa22b-1de4-4cf7-9890-ed44d69937ce

import Mathlib
import Definitions.Def_Maldacena1999_Defs

set_option autoImplicit false

open Filter Topology in
theorem solution (Rt : ℝ) (hRt : 0 < Rt) (c : ℝ) (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioi (-1 / Rt ^ 4))) :
    (∀ z ∈ Set.Ioi (-1 / Rt ^ 4), f z + c = 2 * (z + 1 / Rt ^ 4) * deriv f z) ↔
      ∃ b : ℝ, ∀ z ∈ Set.Ioi (-1 / Rt ^ 4), f z = b * Real.sqrt (1 + Rt ^ 4 * z) - c := by
  have hR4 : 0 < Rt ^ 4 := by positivity
  have hw : ∀ z ∈ Set.Ioi (-1 / Rt ^ 4), 0 < 1 + Rt ^ 4 * z := by
    intro z hz
    have hz' : -1 / Rt ^ 4 < z := hz
    rw [div_lt_iff₀ hR4] at hz'
    linarith
  have hsq : ∀ z ∈ Set.Ioi (-1 / Rt ^ 4), HasDerivAt (fun y => Real.sqrt (1 + Rt ^ 4 * y))
      (Rt ^ 4 / (2 * Real.sqrt (1 + Rt ^ 4 * z))) z := by
    intro z hz
    have h1 : HasDerivAt (fun y : ℝ => 1 + Rt ^ 4 * y) (Rt ^ 4) z := by
      simpa using ((hasDerivAt_id z).const_mul (Rt ^ 4)).const_add 1
    exact h1.sqrt (hw z hz).ne'
  constructor
  · intro hODE
    set g : ℝ → ℝ := fun y => (f y + c) / Real.sqrt (1 + Rt ^ 4 * y) with hg
    have hgd : ∀ z ∈ Set.Ioi (-1 / Rt ^ 4), HasDerivAt g 0 z := by
      intro z hz
      have hfz : HasDerivAt f (deriv f z) z :=
        (hf.differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
      have hs0 : 0 < Real.sqrt (1 + Rt ^ 4 * z) := Real.sqrt_pos.mpr (hw z hz)
      have hs2 : Real.sqrt (1 + Rt ^ 4 * z) ^ 2 = 1 + Rt ^ 4 * z := Real.sq_sqrt (hw z hz).le
      have hd := (hfz.add_const c).div (hsq z hz) hs0.ne'
      have hO := hODE z hz
      have hO' : Rt ^ 4 * (f z + c) = 2 * (Rt ^ 4 * z + 1) * deriv f z := by
        rw [hO]; field_simp
      have key : (f z + c) * (Rt ^ 4 / (2 * Real.sqrt (1 + Rt ^ 4 * z))) =
          deriv f z * Real.sqrt (1 + Rt ^ 4 * z) := by
        rw [mul_div_assoc', div_eq_iff (by positivity)]
        linear_combination hO' - 2 * deriv f z * hs2
      exact hd.congr_deriv (by rw [key, sub_self, zero_div])
    have hdiff : DifferentiableOn ℝ g (Set.Ioi (-1 / Rt ^ 4)) :=
      fun z hz => (hgd z hz).differentiableAt.differentiableWithinAt
    have hderiv : Set.EqOn (deriv g) 0 (Set.Ioi (-1 / Rt ^ 4)) :=
      fun z hz => (hgd z hz).deriv
    obtain ⟨a, ha⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hderiv
    refine ⟨a, fun z hz => ?_⟩
    have h1 := ha z hz
    have hs0 : 0 < Real.sqrt (1 + Rt ^ 4 * z) := Real.sqrt_pos.mpr (hw z hz)
    rw [hg] at h1
    simp only at h1
    rw [div_eq_iff hs0.ne'] at h1
    linarith
  · rintro ⟨b, hb⟩ z hz
    have heq : f =ᶠ[𝓝 z] fun y => b * Real.sqrt (1 + Rt ^ 4 * y) - c := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy using hb y hy
    have hd : HasDerivAt (fun y => b * Real.sqrt (1 + Rt ^ 4 * y) - c)
        (b * (Rt ^ 4 / (2 * Real.sqrt (1 + Rt ^ 4 * z)))) z :=
      ((hsq z hz).const_mul b).sub_const c
    have hs0 : 0 < Real.sqrt (1 + Rt ^ 4 * z) := Real.sqrt_pos.mpr (hw z hz)
    have hs2 : Real.sqrt (1 + Rt ^ 4 * z) ^ 2 = 1 + Rt ^ 4 * z := Real.sq_sqrt (hw z hz).le
    rw [heq.deriv_eq, hd.deriv, hb z hz]
    have e1 : 2 * (z + 1 / Rt ^ 4) * (b * (Rt ^ 4 / (2 * Real.sqrt (1 + Rt ^ 4 * z)))) =
        b * ((1 + Rt ^ 4 * z) / Real.sqrt (1 + Rt ^ 4 * z)) := by
      field_simp
      ring
    have e2 : (1 + Rt ^ 4 * z) / Real.sqrt (1 + Rt ^ 4 * z) = Real.sqrt (1 + Rt ^ 4 * z) := by
      rw [div_eq_iff hs0.ne', ← sq, hs2]
    rw [e1, e2]
    ring
