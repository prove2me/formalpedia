-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_norm_sub_le_two_candidateMaximum_different_axes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:15:56.774183+00:00
-- url     : https://prove2.me/submissions/3223fac4-04f0-46f6-af98-bc19a2beda32

module
public import Definitions.Def_NewtonianLipschitz_CommonSafeFace
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Theorems.Thm_NewtonianLipschitz_cartesian_different_axes_two_hop_bridge
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_norm_sub_le_candidateMaximum_common_face
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_nonneg
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
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x y : Vec3) (d : ℝ)
    (hd : 0 < d) (i j : Fin 3) (hij : i ≠ j)
    (hxi : d ≤ x i ∨ x i ≤ -d)
    (hyj : d ≤ y j ∨ y j ≤ -d) :
    ‖c.accelerationField x - c.accelerationField y‖ ≤
      (2 * ((1 / d ^ 3) *
        (c.gravitationalParameter * candidateMaximum))) * ‖x - y‖ := by
  obtain ⟨w, hwi, hwj, hxw, hwy⟩ :=
    cartesian_different_axes_two_hop_bridge x y i j hij
  have hxface :
      ∃ k : Fin 3,
        (d ≤ x k ∧ d ≤ w k) ∨
        (x k ≤ -d ∧ w k ≤ -d) := by
    refine ⟨i, ?_⟩
    rcases hxi with hiPos | hiNeg
    · left
      exact ⟨hiPos, by rwa [hwi]⟩
    · right
      exact ⟨hiNeg, by rwa [hwi]⟩
  have hyface :
      ∃ k : Fin 3,
        (d ≤ w k ∧ d ≤ y k) ∨
        (w k ≤ -d ∧ y k ≤ -d) := by
    refine ⟨j, ?_⟩
    rcases hyj with hjPos | hjNeg
    · left
      exact ⟨by rwa [hwj], hjPos⟩
    · right
      exact ⟨by rwa [hwj], hjNeg⟩
  let A : ℝ :=
    (1 / d ^ 3) * (c.gravitationalParameter * candidateMaximum)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity)
      (mul_nonneg c.gravitationalParameter_nonneg
        candidateMaximum_nonneg)
  have hxbound :
      ‖c.accelerationField x - c.accelerationField w‖ ≤
        A * ‖x - w‖ :=
    c.accelerationField_norm_sub_le_candidateMaximum_common_face
      x w d hd hxface
  have hybound :
      ‖c.accelerationField w - c.accelerationField y‖ ≤
        A * ‖w - y‖ :=
    c.accelerationField_norm_sub_le_candidateMaximum_common_face
      w y d hd hyface
  change ‖c.accelerationField x - c.accelerationField y‖ ≤
    (2 * A) * ‖x - y‖
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
end NewtonianPointSource
end NewtonianLipschitz
