-- Prove2me | solution 1 for NewtonianLipschitz.euclideanRadius_ge_of_cartesian_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:30:22.500202+00:00
-- url     : https://prove2.me/submissions/7076c301-ffb9-4629-8423-da311aabb363

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
public import Theorems.Thm_NewtonianLipschitz_cartesian_norm_le_euclideanRadius
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (x : Vec3) (d : ℝ)
    (hclear : d ≤ dist x (0 : Vec3)) :
    d ≤ euclideanRadius x := by
  calc
    d ≤ dist x (0 : Vec3) := hclear
    _ = ‖x‖ := by simp
    _ ≤ euclideanRadius x := cartesian_norm_le_euclideanRadius x
end NewtonianLipschitz
