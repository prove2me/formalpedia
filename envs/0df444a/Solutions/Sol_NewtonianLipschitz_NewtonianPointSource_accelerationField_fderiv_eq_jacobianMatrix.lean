-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_eq_jacobianMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:45:08.807194+00:00
-- url     : https://prove2.me/submissions/14d3dbca-975d-4919-8de3-9a9fdaf349b4

module
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Definitions.Def_NewtonianLipschitz_JacobianRows
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_inner_eq_dotProduct
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_mulVec
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_full


set_option autoImplicit true
@[expose] public section
public section
open Matrix WithLp
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x h : Vec3) (hx : x ≠ 0) :
    (fderiv ℝ c.accelerationField x) h =
      newtonianJacobianMatrix c.gravitationalParameter x *ᵥ h := by
  rw [c.accelerationField_fderiv_full x h hx,
    newtonianJacobianMatrix_mulVec c.gravitationalParameter x h hx,
    toPhysicalVec3_inner_eq_dotProduct]
end NewtonianPointSource
end NewtonianLipschitz
