-- Prove2me | solution 1 for HryniewiczCriterion.ambient_positive_czIndex_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T15:26:22.040736+00:00
-- url     : https://prove2.me/submissions/f2037d71-cbea-4a80-8186-484f03d1a1c3

import Theorems.Thm_HryniewiczCriterion_exists_homogeneous_convex_model
import Theorems.Thm_HryniewiczCriterion_homogeneous_windingInterval_gt_one
import Theorems.Thm_HryniewiczCriterion_linearizedXiPath_isSymplecticPath
import Theorems.Thm_HryniewiczCriterion_windingInterval_narrow
import Theorems.Thm_HryniewiczCriterion_czIndexOfPath_ge_three_iff

open HryniewiczCriterion
open scoped ContDiff

theorem solution
    (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) x v v)
    (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4))
    (hY : IsLinearizedFlow H P.x Y) :
    3 ≤ czIndexOfPath (linearizedXiPath H P Y) := by
  obtain ⟨K, hK, -, hA⟩ := exists_homogeneous_convex_model H hS hpos
  obtain ⟨Q, Z, hZ, hWI⟩ := hA P Y hY
  have hgt := homogeneous_windingInterval_gt_one K hK Q Z hZ
  rw [hWI] at hgt
  obtain ⟨hs, hdet, h0⟩ := linearizedXiPath_isSymplecticPath H hS P Y hY
  obtain ⟨a, b, hab, hw, hwid⟩ := windingInterval_narrow _ hs hdet h0
  exact (czIndexOfPath_ge_three_iff _ a b hab hw (by linarith)).2 hgt
