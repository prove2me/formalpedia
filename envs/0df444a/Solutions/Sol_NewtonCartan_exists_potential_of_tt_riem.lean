-- Prove2me | solution 1 for NewtonCartan.exists_potential_of_tt_riem
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:37:59.814687+00:00
-- url     : https://prove2.me/submissions/5d6e07cb-e84a-45cb-a136-40e3908b2be3

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_riem00_spatial_closed_F
import Theorems.Thm_NewtonCartan_exists_potential_of_spatial_F
import Theorems.Thm_NewtonCartan_gauge_NG_poisson_of_spatial_hess

open scoped ContDiff
open Classical
open NewtonCartan

/-! Trautman recovery: spatial F-closedness → spatial Poincaré → gauge NG + Poisson. -/

theorem solution (Γt : Conn) (ρ : E → ℝ)
    (hΓt : IsClassical Γt) (hρ : ContDiff ℝ ∞ ρ) (hcurv : CurvConds Γt ρ)
    (hform : ∀ x a b c d,
      riem Γt x a b c d =
        tt b * (tt c * riem Γt x a 0 0 d - tt d * riem Γt x a 0 0 c)) :
    ∃ φ : E → ℝ, IsNG (gaugeΓ Γt φ) φ ∧ Poisson (gaugeΓ Γt φ) φ ρ := by
  have hF := riem00_spatial_closed_F Γt ρ hΓt hρ hcurv hform
  obtain ⟨hFcont, hrow, hcol, hsym, hclosed, _htr⟩ := hF
  obtain ⟨φ, hφ, hhess⟩ :=
    exists_potential_of_spatial_F (fun x a d => riem Γt x a 0 0 d)
      hFcont hrow hcol hsym hclosed
  refine ⟨φ, ?_⟩
  exact gauge_NG_poisson_of_spatial_hess Γt ρ φ hΓt hρ hcurv hφ hform hhess
