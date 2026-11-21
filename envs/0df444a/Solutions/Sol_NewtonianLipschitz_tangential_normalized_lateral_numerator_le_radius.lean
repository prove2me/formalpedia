-- Prove2me | solution 1 for NewtonianLipschitz.tangential_normalized_lateral_numerator_le_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:59:47.178689+00:00
-- url     : https://prove2.me/submissions/70d8b3cc-f4f2-49a6-b421-6d9fbe22a8c8

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
public import Theorems.Thm_NewtonianLipschitz_tangential_normalized_radius_bounds
public import Theorems.Thm_NewtonianLipschitz_tangential_lateral_row_le_five_four_quadratic


set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |2 * u ^ 2 - 1 - v ^ 2| + 3 * u * v ≤
      (5 / 4 : ℝ) * euclideanRadius (normalizedVector u v) ^ 5 := by
  have hquad :=
    (tangential_normalized_radius_bounds u v).2
  have hnum :=
    tangential_lateral_row_le_five_four_quadratic u v hu hv
  calc
    |2 * u ^ 2 - 1 - v ^ 2| + 3 * u * v ≤
        (5 / 4 : ℝ) * (1 + u ^ 2 + v ^ 2) ^ 2 := hnum
    _ ≤ (5 / 4 : ℝ) *
          euclideanRadius (normalizedVector u v) ^ 5 :=
      mul_le_mul_of_nonneg_left hquad (by norm_num)
end NewtonianLipschitz
