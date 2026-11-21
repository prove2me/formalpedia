-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:43:27.563166+00:00
-- url     : https://prove2.me/submissions/b12ce024-53dc-4a1e-b74e-67f46293ba32

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_product_of_ne_zero
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_radialCoefficient_fderiv_full
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
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x h : Vec3) (hx : x ≠ 0) :
    (fderiv ℝ c.accelerationField x) h =
      (-(c.gravitationalParameter) / euclideanRadius x ^ 3) • h +
        ((3 * c.gravitationalParameter / euclideanRadius x ^ 5) *
            ⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ) • x := by
  rw [c.accelerationField_fderiv_product_of_ne_zero x hx]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply]
  rw [c.radialCoefficient_fderiv_full x h hx]
  rfl
end NewtonianPointSource
end NewtonianLipschitz
