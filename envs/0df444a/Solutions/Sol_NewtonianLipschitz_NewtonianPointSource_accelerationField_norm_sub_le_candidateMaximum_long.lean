-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_long
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:57:44.41019+00:00
-- url     : https://prove2.me/submissions/7a821d8c-02fb-4a9b-b2d5-fb845a0f8608

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_ge_two
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_le_of_cartesian_clearance
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_nonneg


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource)
    (x y : Vec3) (d : ℝ)
    (hd : 0 < d)
    (hx : d ≤ ‖x‖) (hy : d ≤ ‖y‖)
    (hsep : d ≤ ‖x - y‖) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * candidateMaximum)) *
          ‖x - y‖ := by
  have hmass : 2 * c.gravitationalParameter ≤
      c.gravitationalParameter * candidateMaximum := by
    calc
      2 * c.gravitationalParameter =
        c.gravitationalParameter * 2 := by ring
      _ ≤ c.gravitationalParameter * candidateMaximum :=
        mul_le_mul_of_nonneg_left candidateMaximum_ge_two
          c.gravitationalParameter_nonneg
  have hscale :
      (1 / d ^ 3) * (2 * c.gravitationalParameter) ≤
        (1 / d ^ 3) *
          (c.gravitationalParameter * candidateMaximum) :=
    mul_le_mul_of_nonneg_left hmass (by positivity)
  have hcoef :
      0 ≤ (1 / d ^ 3) *
        (c.gravitationalParameter * candidateMaximum) :=
    mul_nonneg (by positivity)
      (mul_nonneg c.gravitationalParameter_nonneg
        candidateMaximum_nonneg)
  calc
    ‖c.accelerationField x - c.accelerationField y‖ ≤
        ‖c.accelerationField x‖ + ‖c.accelerationField y‖ :=
      norm_sub_le _ _
    _ ≤ c.gravitationalParameter / d ^ 2 +
        c.gravitationalParameter / d ^ 2 :=
      add_le_add
        (c.accelerationField_norm_le_of_cartesian_clearance x d hd hx)
        (c.accelerationField_norm_le_of_cartesian_clearance y d hd hy)
    _ = 2 * (c.gravitationalParameter / d ^ 2) := by ring
    _ = ((1 / d ^ 3) * (2 * c.gravitationalParameter)) * d := by
      field_simp [ne_of_gt hd]
    _ ≤ ((1 / d ^ 3) *
          (c.gravitationalParameter * candidateMaximum)) * d :=
      mul_le_mul_of_nonneg_right hscale hd.le
    _ ≤ ((1 / d ^ 3) *
          (c.gravitationalParameter * candidateMaximum)) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_left hsep hcoef
end NewtonianPointSource
end NewtonianLipschitz
