-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:07:10.425887+00:00
-- url     : https://prove2.me/submissions/f1291cca-4fa4-4cd5-a5ba-1e03c6e7a97f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H0_finite
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H1_finite
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H2_finite
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_lineBundle_cohomology_zero_above_two

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI OAI.MaximalSeshadri.Geometry
open OAI.MaximalSeshadri.Frames OAI.MaximalSeshadri.Projective

theorem solution (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf n) := by
  cases n with
  | zero => exact S.H0_finite A hA L
  | succ n => cases n with
    | zero => exact S.H1_finite A hA L
    | succ n => cases n with
      | zero => exact S.H2_finite A hA L
      | succ n =>
        let := Module.compHom (cohomology L.sheaf (n+3)) (baseScalars S.structureMap)
        let : Subsingleton (cohomology L.sheaf (n+3)) := ⟨fun x y =>
          (S.lineBundle_cohomology_zero_above_two A hA L n x).trans
            (S.lineBundle_cohomology_zero_above_two A hA L n y).symm⟩
        infer_instance
