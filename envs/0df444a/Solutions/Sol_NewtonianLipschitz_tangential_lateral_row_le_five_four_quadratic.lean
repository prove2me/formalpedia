-- Prove2me | solution 1 for NewtonianLipschitz.tangential_lateral_row_le_five_four_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:58:06.030962+00:00
-- url     : https://prove2.me/submissions/9a4f7067-2c5d-4495-8495-69bbd30427a6

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
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
theorem _root_.solution
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |2 * u ^ 2 - 1 - v ^ 2| + 3 * u * v ≤
      (5 / 4 : ℝ) * (1 + u ^ 2 + v ^ 2) ^ 2 := by
  let t : ℝ := u ^ 2 + v ^ 2
  have h_abs :
      |2 * u ^ 2 - 1 - v ^ 2| ≤
        1 + 2 * u ^ 2 + v ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg u, sq_nonneg v]
  have h_product : 3 * u * v ≤ (3 / 2 : ℝ) * t := by
    dsimp [t]
    nlinarith [sq_nonneg (u - v)]
  have h_base :
      1 + 2 * u ^ 2 + v ^ 2 ≤ 1 + 2 * t := by
    dsimp [t]
    nlinarith [sq_nonneg v]
  have h_quadratic :
      1 + (7 / 2 : ℝ) * t ≤ (5 / 4 : ℝ) * (1 + t) ^ 2 := by
    nlinarith [sq_nonneg (5 * t - 2)]
  calc
    |2 * u ^ 2 - 1 - v ^ 2| + 3 * u * v
        ≤ (1 + 2 * u ^ 2 + v ^ 2) + 3 * u * v :=
          add_le_add h_abs le_rfl
    _ ≤ (1 + 2 * t) + (3 / 2 : ℝ) * t :=
          add_le_add h_base h_product
    _ = 1 + (7 / 2 : ℝ) * t := by ring
    _ ≤ (5 / 4 : ℝ) * (1 + t) ^ 2 := h_quadratic
    _ = (5 / 4 : ℝ) * (1 + u ^ 2 + v ^ 2) ^ 2 := by
      rw [show t = u ^ 2 + v ^ 2 from rfl]
      ring
end NewtonianLipschitz
