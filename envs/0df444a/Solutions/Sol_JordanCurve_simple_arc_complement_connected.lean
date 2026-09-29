-- Prove2me | solution 1 for JordanCurve.simple_arc_complement_connected
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T12:54:53.57476+00:00
-- url     : https://prove2.me/submissions/6844d300-4b0b-425f-ad6b-1a49fe8b8795

import Definitions.Def_Schoenflies_SquareCycle
import Theorems.Thm_JordanCurve_subtype_arc_is_schoenflies_arc

theorem solution
    (α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (hα : Continuous α) (hinj : Function.Injective α) :
    IsConnected ((Set.range α)ᶜ) := by
  exact Schoenflies.isConnected_compl_arc
    (JordanCurve.subtype_arc_is_schoenflies_arc α hα hinj)
    Schoenflies.squaresTwoConnected
