-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:47:45.434667+00:00
-- url     : https://prove2.me/submissions/95fedc45-68e6-4215-bd59-22a5174b0611
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_pow
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_exists_positive_ambient_power

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open OAI.MaximalSeshadri.Frames OAI.MaximalSeshadri.Projective
open OAI.MaximalSeshadri.Geometry

theorem solution (S : Surface) (C : IntegralCurve S)
    (L : LineBundle S.scheme) (hL : L.IsAmple) : 0 < curveDegree S L C := by
  obtain ⟨m, hm, hp⟩ := C.exists_positive_ambient_power S L hL
  rw [curveDegree_pow S L hL] at hp
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  nlinarith
