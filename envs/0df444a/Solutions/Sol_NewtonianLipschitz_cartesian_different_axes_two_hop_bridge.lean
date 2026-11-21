-- Prove2me | solution 1 for NewtonianLipschitz.cartesian_different_axes_two_hop_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:46:51.926482+00:00
-- url     : https://prove2.me/submissions/9a3c4312-99d5-45d7-902d-6ea6baa6cfad

module
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
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
    (x y : Vec3) (i j : Fin 3) (hij : i ≠ j) :
    ∃ w : Vec3,
      w i = x i ∧
      w j = y j ∧
      ‖x - w‖ ≤ ‖x - y‖ ∧
      ‖w - y‖ ≤ ‖x - y‖ := by
  let w : Vec3 := fun k => if k = i then x i else y k
  have hwi : w i = x i := by
    simp [w]
  have hwj : w j = y j := by
    simp [w, hij.symm]
  have hxw : ‖x - w‖ ≤ ‖x - y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).2
    intro k
    by_cases hki : k = i
    · subst k
      have hzero : (x - w) i = 0 := by
        simp [w]
      simpa [hzero] using (norm_nonneg (x - y))
    · have heq : (x - w) k = (x - y) k := by
        simp [w, hki]
      rw [heq]
      exact norm_le_pi_norm (x - y) k
  have hwy : ‖w - y‖ ≤ ‖x - y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).2
    intro k
    by_cases hki : k = i
    · subst k
      have heq : (w - y) i = (x - y) i := by
        simp [w]
      rw [heq]
      exact norm_le_pi_norm (x - y) i
    · have hzero : (w - y) k = 0 := by
        simp [w, hki]
      simpa [hzero] using (norm_nonneg (x - y))
  exact ⟨w, hwi, hwj, hxw, hwy⟩
end NewtonianLipschitz
