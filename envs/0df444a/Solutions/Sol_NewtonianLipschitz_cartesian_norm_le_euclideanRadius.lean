-- Prove2me | solution 1 for NewtonianLipschitz.cartesian_norm_le_euclideanRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:24:16.82167+00:00
-- url     : https://prove2.me/submissions/cb086622-6930-477e-9a2d-bd1cb1177f37

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
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
theorem _root_.solution (x : Vec3) :
    ‖x‖ ≤ euclideanRadius x := by
  rw [euclideanRadius_eq_physical_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (toPhysicalVec3 x))).2
  intro i
  simpa only [toPhysicalVec3_apply] using
    (PiLp.norm_apply_le (toPhysicalVec3 x) i)
end NewtonianLipschitz
