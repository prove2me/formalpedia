-- Prove2me | solution 1 for NewtonGravitation.gravField_uniformShell_inside
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T12:05:27.036181+00:00
-- url     : https://prove2.me/submissions/bd7ce850-1977-4d0c-ad5c-bc7ab2e2d9c7

import Definitions.Def_NewtonGravitation_Defs
import Theorems.Thm_NewtonGravitation_uniformShell_geometry
import Theorems.Thm_NewtonGravitation_gravField_eq_zero_of_symmetric_outside
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (M : NNReal) (a : ℝ) (ha : 0 < a)
    (x : Space) (hx : ‖x‖ < a) :
    gravField (uniformShell M a) x = 0 := by
  classical
  have hgeo := NewtonGravitation.uniformShell_geometry M a ha
  letI : IsFiniteMeasure (uniformShell M a) := hgeo.1
  have hsym : IsSphericallySymmetric (uniformShell M a) := hgeo.2.1
  have hzero : (uniformShell M a) (Metric.ball (0 : Space) a) = 0 := hgeo.2.2
  exact NewtonGravitation.gravField_eq_zero_of_symmetric_outside
    (uniformShell M a) hsym a hzero x hx
