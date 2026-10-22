-- Prove2me | solution 1 for LeveragedPayouts.ShockSize.lstar_lt_labor
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:24:21.066067+00:00
-- url     : https://prove2.me/submissions/71b193c0-462a-4daf-b1f4-f4a5623501e7

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

set_option autoImplicit false
open LeveragedPayouts.Unregulated

theorem solution (E : LeveragedPayouts.Unregulated.Economy) (r l : ℝ) (hr0 : 0 < r) (hrR : r < E.R)
    (hl : LeveragedPayouts.Unregulated.IsLaborDemand E r l) : E.lstar < l := by
  obtain ⟨hf0, hfc, hfd, hfp, hfn, -, -⟩ := E.hf
  have hanti : StrictAntiOn (deriv E.f) (Set.Ioi 0) := by
    have hd1 : ContDiffOn ℝ 1 (deriv E.f) (Set.Ioi 0) :=
      hfd.deriv_of_isOpen isOpen_Ioi (by norm_num)
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0) hd1.continuousOn
    intro x hx
    rw [interior_Ioi] at hx
    exact hfn x hx
  obtain ⟨hlpos, hl1, hleq⟩ := hl
  have hmin : min r E.R = r := min_eq_left hrR.le
  rw [hmin] at hleq
  have hR := E.hR
  have hπ := E.hπ0
  have hw : E.wstar = E.π / (2 * E.R) * deriv E.f E.lstar := by
    rw [← E.hw, ← E.h20]
  rw [hw] at hleq
  have hb : 0 < deriv E.f E.lstar := hfp _ E.hl0
  have h2R : 0 < 2 * E.R - r := by linarith
  have hkey : E.R ^ 2 * deriv E.f l = r * (E.R * 2 - r) * deriv E.f E.lstar := by
    field_simp at hleq
    rw [div_eq_iff (by linarith : (0:ℝ) < E.R * 2 - r).ne'] at hleq
    linarith
  have hlt : deriv E.f l < deriv E.f E.lstar := by
    have h4 : E.R ^ 2 * deriv E.f l < E.R ^ 2 * deriv E.f E.lstar := by
      nlinarith [mul_pos (sq_pos_of_pos (sub_pos.mpr hrR)) hb]
    exact lt_of_mul_lt_mul_left h4 (by positivity)
  by_contra hcon
  push Not at hcon
  have := hanti.antitoneOn hlpos (E.hl0 : (0:ℝ) < E.lstar) hcon
  linarith
