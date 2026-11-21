-- Prove2me | solution 1 for NewtonianLipschitz.toPhysicalVec3_norm_le_two_cartesian_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:23.761298+00:00
-- url     : https://prove2.me/submissions/c211939a-4107-48c0-b3a0-070eb0987cce

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_le_two_mul_cartesian_norm
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm


set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (x : Vec3) :
    ‖toPhysicalVec3 x‖ ≤ 2 * ‖x‖ := by
  rw [← euclideanRadius_eq_physical_norm]
  exact euclideanRadius_le_two_mul_cartesian_norm x
end NewtonianLipschitz
