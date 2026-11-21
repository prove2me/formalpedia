-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_candidateMaximum_different_axes_of_safePlane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:59:43.202748+00:00
-- url     : https://prove2.me/submissions/d7d71191-0012-48bd-8013-8badf9f9e08b

module
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_cons
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_nil
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_gt_five_halves
public import Theorems.Thm_NewtonianLipschitz_cartesian_different_axes_two_hop_bridge
public import Theorems.Thm_NewtonianLipschitz_coordinateAbs_apply
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_one
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_two
public import Theorems.Thm_NewtonianLipschitz_cycleIndex_zero
public import Theorems.Thm_NewtonianLipschitz_cycleVec_one
public import Theorems.Thm_NewtonianLipschitz_cycleVec_two
public import Theorems.Thm_NewtonianLipschitz_cycleVec_zero
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_one
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_two
public import Theorems.Thm_NewtonianLipschitz_normalizedVector_zero
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_one
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_two
public import Theorems.Thm_NewtonianLipschitz_swapYZIndex_zero
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_one
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_two
public import Theorems.Thm_NewtonianLipschitz_swapYZVec_zero
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_cons
attribute [local simp] NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_nil
attribute [local simp] NewtonianLipschitz.coordinateAbs_apply
attribute [local simp] NewtonianLipschitz.cycleIndex_one
attribute [local simp] NewtonianLipschitz.cycleIndex_two
attribute [local simp] NewtonianLipschitz.cycleIndex_zero
attribute [local simp] NewtonianLipschitz.cycleVec_one
attribute [local simp] NewtonianLipschitz.cycleVec_two
attribute [local simp] NewtonianLipschitz.cycleVec_zero
attribute [local simp] NewtonianLipschitz.normalizedVector_one
attribute [local simp] NewtonianLipschitz.normalizedVector_two
attribute [local simp] NewtonianLipschitz.normalizedVector_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.swapYZIndex_one
attribute [local simp] NewtonianLipschitz.swapYZIndex_two
attribute [local simp] NewtonianLipschitz.swapYZIndex_zero
attribute [local simp] NewtonianLipschitz.swapYZVec_one
attribute [local simp] NewtonianLipschitz.swapYZVec_two
attribute [local simp] NewtonianLipschitz.swapYZVec_zero
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (hPlane : oneSourceSafePlaneFiveFourthBound)
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ)
    (hd : 0 < d) (i j : Fin 3) (hij : i ≠ j)
    (hxi : d ≤ x i ∨ x i ≤ -d)
    (hyj : d ≤ y j ∨ y j ≤ -d) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      ((1 / d ^ 3) *
        (c.gravitationalParameter * candidateMaximum)) * ‖x - y‖ := by
  obtain ⟨w, hwi, hwj, hxw, hwy⟩ :=
    cartesian_different_axes_two_hop_bridge x y i j hij
  have hwj_safe : d ≤ w j ∨ w j ≤ -d := by
    simpa only [hwj] using hyj
  let A : ℝ :=
    (1 / d ^ 3) * (c.gravitationalParameter * (5 / 4 : ℝ))
  let B : ℝ :=
    (1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity)
      (mul_nonneg c.gravitationalParameter_nonneg (by norm_num))
  have hcoef : 2 * A ≤ B := by
    have hm :
        c.gravitationalParameter * (5 / 2 : ℝ) ≤
          c.gravitationalParameter * candidateMaximum :=
      mul_le_mul_of_nonneg_left
        (le_of_lt candidateMaximum_gt_five_halves)
        c.gravitationalParameter_nonneg
    calc
      2 * A =
          (1 / d ^ 3) *
            (c.gravitationalParameter * (5 / 2 : ℝ)) := by
        dsimp [A]
        ring
      _ ≤ B := by
        dsimp [B]
        exact mul_le_mul_of_nonneg_left hm (by positivity)
  have hxbound :
      ‖c.accelerationField x - c.accelerationField w‖ ≤
        A * ‖x - w‖ :=
    hPlane c x w d i hd hwi.symm hxi
  have hybound :
      ‖c.accelerationField w - c.accelerationField y‖ ≤
        A * ‖w - y‖ :=
    hPlane c w y d j hd hwj hwj_safe
  change ‖c.accelerationField x - c.accelerationField y‖ ≤
    B * ‖x - y‖
  calc
    ‖c.accelerationField x - c.accelerationField y‖ ≤
        ‖c.accelerationField x - c.accelerationField w‖ +
          ‖c.accelerationField w - c.accelerationField y‖ := by
      simpa only [dist_eq_norm] using
        (dist_triangle
          (c.accelerationField x)
          (c.accelerationField w)
          (c.accelerationField y))
    _ ≤ A * ‖x - w‖ + A * ‖w - y‖ :=
      add_le_add hxbound hybound
    _ ≤ A * ‖x - y‖ + A * ‖x - y‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hxw hA)
        (mul_le_mul_of_nonneg_left hwy hA)
    _ = (2 * A) * ‖x - y‖ := by ring
    _ ≤ B * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
end NewtonianPointSource
end NewtonianLipschitz
