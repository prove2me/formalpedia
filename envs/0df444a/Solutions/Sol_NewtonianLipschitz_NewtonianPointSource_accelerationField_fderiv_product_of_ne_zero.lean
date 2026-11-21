-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_fderiv_product_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:50.415125+00:00
-- url     : https://prove2.me/submissions/7e06ad2f-e8cf-494b-b64d-1ce58799c256

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_fderiv_product
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_radialCoefficient_differentiableAt_of_ne_zero

set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) (hx : x ≠ 0) :
    fderiv ℝ c.accelerationField x =
      c.radialCoefficient x • ContinuousLinearMap.id ℝ Vec3 +
        (fderiv ℝ c.radialCoefficient x).smulRight x := by
  exact c.accelerationField_fderiv_product x
    (c.radialCoefficient_differentiableAt_of_ne_zero x hx)
end NewtonianPointSource
end NewtonianLipschitz
