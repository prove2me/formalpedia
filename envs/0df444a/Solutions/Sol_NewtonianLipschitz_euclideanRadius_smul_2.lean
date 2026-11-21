-- Prove2me | solution 2 for NewtonianLipschitz.euclideanRadius_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:46:20.315176+00:00
-- url     : https://prove2.me/submissions/c60e5ce6-8015-4129-82a5-80ff67f96c7f

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_eq_continuousLinearEquiv


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution (c : ℝ) (x : Vec3) :
    euclideanRadius (c • x) = |c| * euclideanRadius x := by
  rw [euclideanRadius_eq_physical_norm (c • x),
    euclideanRadius_eq_physical_norm x,
    toPhysicalVec3_eq_continuousLinearEquiv (c • x),
    toPhysicalVec3_eq_continuousLinearEquiv x]
  rw [map_smul, norm_smul, Real.norm_eq_abs]
end NewtonianLipschitz
