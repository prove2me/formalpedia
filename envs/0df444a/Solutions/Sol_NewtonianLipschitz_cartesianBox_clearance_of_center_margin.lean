-- Prove2me | solution 1 for NewtonianLipschitz.cartesianBox_clearance_of_center_margin
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:41:47.356315+00:00
-- url     : https://prove2.me/submissions/eaa22785-f419-4ba9-abbf-eaf60373e289

module
public import Definitions.Def_NewtonianLipschitz_ConvexSharp
public import Definitions.Def_NewtonianLipschitz_CartesianBoxSharp
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz


theorem solution
    (anchor : Vec3) (ρ d : ℝ) (hd : 0 < d)
    (hmargin : d + ρ ≤ dist anchor (0 : Vec3)) :
    ∀ z ∈ Metric.ball anchor ρ, d ≤ ‖z‖ := by
  intro z hz
  have ht := dist_triangle anchor z (0 : Vec3)
  rw [dist_comm anchor z] at ht
  simp only [dist_zero_right] at ht hmargin
  have h := Metric.mem_ball.mp hz
  linarith
