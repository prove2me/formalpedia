-- Prove2me | solution 2 for MasulloRH.logDeriv_analytic_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T22:45:13.308062+00:00
-- url     : https://prove2.me/submissions/5b9fb271-9a9d-4a81-8f71-f9eb094dba72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive
import Theorems.Thm_GRH_grh_critical_line_iff
import Mathlib

open Filter Topology

theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta z / riemannZeta z) s := by
  have hζ : AnalyticAt ℂ riemannZeta s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_ne.mem_nhds hs_one] with z hz
    exact differentiableAt_riemannZeta hz
  have hne : riemannZeta s ≠ 0 := by
    have h := GRH.grh_critical_line_iff.mp AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive
      1 (1 : DirichletCharacter ℂ 1) s hs (fun h => hs_one h.2)
    rwa [DirichletCharacter.LFunction_modOne_eq] at h
  exact hζ.deriv.div hζ hne
