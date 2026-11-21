-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_le_of_cartesian_clearance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:55:57.619779+00:00
-- url     : https://prove2.me/submissions/7ea655af-2401-4ff0-b062-f3e1eda52f9e

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Definitions.Def_NewtonianLipschitz_LongSeparation
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_eq_formula
public import Theorems.Thm_NewtonianLipschitz_cartesian_norm_le_euclideanRadius


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) (d : ℝ)
    (hd : 0 < d) (hclear : d ≤ ‖x‖) :
    ‖c.accelerationField x‖ ≤ c.gravitationalParameter / d ^ 2 := by
  have hrclear : d ≤ euclideanRadius x :=
    hclear.trans (cartesian_norm_le_euclideanRadius x)
  have hr : 0 < euclideanRadius x := lt_of_lt_of_le hd hrclear
  have hcoeff : 0 ≤ c.gravitationalParameter / euclideanRadius x ^ 3 :=
    div_nonneg c.gravitationalParameter_nonneg
      (pow_nonneg (le_of_lt hr) _)
  have hratio :
      c.gravitationalParameter / euclideanRadius x ^ 2 ≤
        c.gravitationalParameter / d ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hr 2) (pow_pos hd 2)).2
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hd.le hrclear 2)
      c.gravitationalParameter_nonneg
  calc
    ‖c.accelerationField x‖ =
        (c.gravitationalParameter / euclideanRadius x ^ 3) * ‖x‖ := by
      rw [c.accelerationField_eq_formula, norm_smul,
        Real.norm_eq_abs, abs_div, abs_neg,
        abs_of_nonneg c.gravitationalParameter_nonneg,
        abs_of_nonneg (pow_nonneg (le_of_lt hr) 3)]
    _ ≤ (c.gravitationalParameter / euclideanRadius x ^ 3) *
          euclideanRadius x :=
      mul_le_mul_of_nonneg_left
        (cartesian_norm_le_euclideanRadius x) hcoeff
    _ = c.gravitationalParameter / euclideanRadius x ^ 2 := by
      field_simp [ne_of_gt hr]
    _ ≤ c.gravitationalParameter / d ^ 2 := hratio
end NewtonianPointSource
end NewtonianLipschitz
