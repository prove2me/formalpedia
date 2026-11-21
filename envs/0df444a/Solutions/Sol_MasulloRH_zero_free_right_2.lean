-- Prove2me | solution 2 for MasulloRH.zero_free_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T22:36:27.681099+00:00
-- url     : https://prove2.me/submissions/acb4bf6d-09a2-48b0-9ee9-4fe0cba2cdc7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive
import Theorems.Thm_GRH_grh_critical_line_iff

theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  have h := GRH.grh_critical_line_iff.mp AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive
    1 (1 : DirichletCharacter ℂ 1) s hs (fun h => hs_one h.2)
  rwa [DirichletCharacter.LFunction_modOne_eq] at h
