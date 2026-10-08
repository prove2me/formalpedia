-- Prove2me | solution 1 for HryniewiczCriterion.strictly_convex_windingInterval_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T22:18:10.770093+00:00
-- url     : https://prove2.me/submissions/e2cd6afa-08e6-4ee1-9ec9-aab8beccbe23

import Theorems.Thm_HryniewiczCriterion_exists_ambient_positive_contact_model
import Theorems.Thm_HryniewiczCriterion_ambient_positive_czIndex_ge_three
import Theorems.Thm_HryniewiczCriterion_linearizedXiPath_isSymplecticPath
import Theorems.Thm_HryniewiczCriterion_windingInterval_narrow
import Theorems.Thm_HryniewiczCriterion_czIndexOfPath_ge_three_iff
import Mathlib.Tactic.Linarith

open HryniewiczCriterion
open scoped ContDiff
set_option autoImplicit false

theorem solution (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hC : IsStrictlyConvexLevel H)
    (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H P.x Y) :
    ∀ d ∈ windingInterval (linearizedXiPath H P Y), 1 < d := by
  obtain ⟨G, hG, _hsurface, hpos, htransfer⟩ := exists_ambient_positive_contact_model H hS hC
  obtain ⟨Q, Z, hZ, heq⟩ := htransfer P Y hY
  have hindex := ambient_positive_czIndex_ge_three G hG hpos Q Z hZ
  obtain ⟨hsmooth, hdet, hzero⟩ := linearizedXiPath_isSymplecticPath G hG Q Z hZ
  obtain ⟨a, b, hab, hw, hwidth⟩ :=
    windingInterval_narrow (linearizedXiPath G Q Z) hsmooth hdet hzero
  have hbound := (czIndexOfPath_ge_three_iff (linearizedXiPath G Q Z) a b hab hw
    (by linarith : b - a < 1)).mp hindex
  simpa only [heq] using hbound
