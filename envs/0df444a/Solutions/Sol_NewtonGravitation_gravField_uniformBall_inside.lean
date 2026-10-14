-- Prove2me | solution 1 for NewtonGravitation.gravField_uniformBall_inside
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T18:13:55.321656+00:00
-- url     : https://prove2.me/submissions/e4953e34-125e-4889-94a9-d6455dc98c02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NewtonGravitation_Defs
import Theorems.Thm_NewtonGravitation_uniformBall_interior_data
import Theorems.Thm_NewtonGravitation_gravField_eq_enclosed_mass
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (M : NNReal) (R : ℝ) (hR : 0 < R)
    (x : Space) (hx : ‖x‖ < R) :
    gravField (uniformBall M R) x = -(G * M / R ^ 3) • x := by
  classical
  have hdata := NewtonGravitation.uniformBall_interior_data M R hR x hx
  letI : IsFiniteMeasure (uniformBall M R) := hdata.1
  have hsym : IsSphericallySymmetric (uniformBall M R) := hdata.2.1
  have hint : Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y))
      (uniformBall M R) := hdata.2.2.1
  have hmass : (uniformBall M R).real (Metric.ball (0 : Space) ‖x‖) =
      (M : ℝ) * (‖x‖ / R) ^ 3 := hdata.2.2.2
  have hfield := NewtonGravitation.gravField_eq_enclosed_mass
    (uniformBall M R) hsym x hint
  rw [hmass] at hfield
  calc
    gravField (uniformBall M R) x =
        pointField ((M : ℝ) * (‖x‖ / R) ^ 3) 0 x := hfield
    _ = -(G * M / R ^ 3) • x := by
      by_cases hx0 : x = 0
      · subst x
        simp [pointField]
      · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
        have hR0 : R ≠ 0 := ne_of_gt hR
        simp only [pointField, sub_zero]
        congr 1
        field_simp
