-- Prove2me | solution 1 for NewtonGravitation.gravField_uniformBall_outside
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T12:17:23.992296+00:00
-- url     : https://prove2.me/submissions/99db809f-5e76-4997-b694-9e3375abf98d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NewtonGravitation_Defs
import Theorems.Thm_NewtonGravitation_gravField_eq_enclosed_mass
import Theorems.Thm_NewtonGravitation_uniformBall_exterior_data
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (M : NNReal) (R : ℝ) (hR : 0 < R)
    (x : Space) (hx : R ≤ ‖x‖) :
    gravField (uniformBall M R) x = pointField M 0 x := by
  classical
  have hdata := NewtonGravitation.uniformBall_exterior_data M R hR x hx
  letI : IsFiniteMeasure (uniformBall M R) := hdata.1
  have hsym : IsSphericallySymmetric (uniformBall M R) := hdata.2.1
  have hint : Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y))
      (uniformBall M R) := hdata.2.2.1
  have hmass : (uniformBall M R).real (Metric.ball (0 : Space) ‖x‖) =
      (M : ℝ) := hdata.2.2.2
  simpa only [hmass] using
    (NewtonGravitation.gravField_eq_enclosed_mass
      (uniformBall M R) hsym x hint)
