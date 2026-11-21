-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_eq_radialCoefficient_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:50.740199+00:00
-- url     : https://prove2.me/submissions/070b3842-64ad-413c-a005-be69fe394c79

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_eq_formula


set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) :
    c.accelerationField x = c.radialCoefficient x • x := by
  rw [c.accelerationField_eq_formula x]
  rfl
end NewtonianPointSource
end NewtonianLipschitz
