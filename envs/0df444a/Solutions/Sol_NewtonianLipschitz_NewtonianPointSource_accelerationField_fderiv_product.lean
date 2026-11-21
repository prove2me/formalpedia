-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:51.195797+00:00
-- url     : https://prove2.me/submissions/29a50518-2a01-43be-beff-1c0c4f6320cc

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_eq_radialCoefficient_smul

set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3)
    (hcoeff : DifferentiableAt ℝ c.radialCoefficient x) :
    fderiv ℝ c.accelerationField x =
      c.radialCoefficient x • ContinuousLinearMap.id ℝ Vec3 +
        (fderiv ℝ c.radialCoefficient x).smulRight x := by
  have hc : HasFDerivAt c.radialCoefficient
      (fderiv ℝ c.radialCoefficient x) x :=
    hcoeff.hasFDerivAt
  have hid : HasFDerivAt (fun y : Vec3 => y)
      (ContinuousLinearMap.id ℝ Vec3) x :=
    hasFDerivAt_id x
  have hsmul := hc.smul hid
  have hfun : c.accelerationField =
      (fun y : Vec3 => c.radialCoefficient y • y) := by
    funext y
    exact c.accelerationField_eq_radialCoefficient_smul y
  rw [hfun]
  exact hsmul.fderiv
end NewtonianPointSource
end NewtonianLipschitz
