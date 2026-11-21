-- Prove2me | solution 1 for NewtonianLipschitz.tangential_normalized_first_numerator_le_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:01:50.633264+00:00
-- url     : https://prove2.me/submissions/3452116f-58a0-4739-bfbd-6887ddb756fb

module
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialNormalized
public import Theorems.Thm_NewtonianLipschitz_tangential_normalized_radius_bounds
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_radius_sq
public import Theorems.Thm_NewtonianLipschitz_tangential_first_row_squared_le_five_four


set_option autoImplicit true
@[expose] public section
public section
open Matrix
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    3 * (u + v) ≤
      (5 / 4 : ℝ) * euclideanRadius (normalizedVector u v) ^ 5 := by
  let r := euclideanRadius (normalizedVector u v)
  have hr1 : 1 ≤ r :=
    (tangential_normalized_radius_bounds u v).1
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hsq : r ^ 2 = 1 + u ^ 2 + v ^ 2 :=
    normalizedVector_radius_sq u v
  have hpower :
      r ^ 10 = (1 + u ^ 2 + v ^ 2) ^ 5 := by
    rw [← hsq]
    ring
  have hbase :=
    tangential_first_row_squared_le_five_four
      u v (u ^ 2 + v ^ 2) rfl
  have hsqbound :
      (3 * (u + v)) ^ 2 ≤
        ((5 / 4 : ℝ) * r ^ 5) ^ 2 := by
    calc
      (3 * (u + v)) ^ 2 ≤
          ((5 / 4 : ℝ) ^ 2) *
            (1 + (u ^ 2 + v ^ 2)) ^ 5 := hbase
      _ = ((5 / 4 : ℝ) * r ^ 5) ^ 2 := by
        rw [show 1 + (u ^ 2 + v ^ 2) =
          1 + u ^ 2 + v ^ 2 by ring, ← hpower]
        ring
  have hfirst : 0 ≤ 3 * (u + v) := by positivity
  have hsecond : 0 < (5 / 4 : ℝ) * r ^ 5 := by positivity
  by_contra hnot
  have hstrict : (5 / 4 : ℝ) * r ^ 5 < 3 * (u + v) :=
    lt_of_not_ge hnot
  have hprod :
      0 < (3 * (u + v) - (5 / 4 : ℝ) * r ^ 5) *
        (3 * (u + v) + (5 / 4 : ℝ) * r ^ 5) :=
    mul_pos (sub_pos.mpr hstrict) (by linarith)
  nlinarith
end NewtonianLipschitz
