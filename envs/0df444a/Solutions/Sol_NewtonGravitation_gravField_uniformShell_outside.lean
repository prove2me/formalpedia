-- Prove2me | solution 1 for NewtonGravitation.gravField_uniformShell_outside
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T12:23:31.477628+00:00
-- url     : https://prove2.me/submissions/4ba50a63-8680-4dcd-8166-88cac0fe03f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NewtonGravitation_Defs
import Theorems.Thm_NewtonGravitation_uniformShell_geometry
import Theorems.Thm_NewtonGravitation_uniformShell_totalMass_support
import Theorems.Thm_NewtonGravitation_shell_theorem_exterior
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (M : NNReal) (a : ℝ) (ha : 0 < a)
    (x : Space) (hx : a < ‖x‖) :
    gravField (uniformShell M a) x = pointField M 0 x := by
  classical
  have hgeo := NewtonGravitation.uniformShell_geometry M a ha
  letI : IsFiniteMeasure (uniformShell M a) := hgeo.1
  have hsym : IsSphericallySymmetric (uniformShell M a) := hgeo.2.1
  have hsupport := NewtonGravitation.uniformShell_totalMass_support M a ha
  have hfield := NewtonGravitation.shell_theorem_exterior
    (uniformShell M a) hsym a hsupport.2 x hx
  rw [hsupport.1] at hfield
  exact hfield
