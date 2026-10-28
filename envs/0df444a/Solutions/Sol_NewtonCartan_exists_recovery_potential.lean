-- Prove2me | solution 1 for NewtonCartan.exists_recovery_potential
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:18:09.78493+00:00
-- url     : https://prove2.me/submissions/ae26d391-cba6-413b-9536-b85460fd3882

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_riem_tt_form_of_curvConds
import Theorems.Thm_NewtonCartan_exists_potential_of_tt_riem

open scoped ContDiff
open Classical
open NewtonCartan

/-! Existence of a recovering potential: CurvConds ⇒ tt-form ⇒ Poincaré/gauge. -/

theorem solution (Γt : Conn) (ρ : E → ℝ)
    (hΓt : IsClassical Γt) (hρ : ContDiff ℝ ∞ ρ) (hcurv : CurvConds Γt ρ) :
    ∃ φ : E → ℝ, IsNG (gaugeΓ Γt φ) φ ∧ Poisson (gaugeΓ Γt φ) φ ρ := by
  refine exists_potential_of_tt_riem Γt ρ hΓt hρ hcurv ?_
  intro x a b c d
  exact riem_tt_form_of_curvConds Γt ρ hΓt hcurv x a b c d
