-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_eq_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:36.919161+00:00
-- url     : https://prove2.me/submissions/e8657bbd-f3c3-4474-bcfd-2ed279ec0133

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Theorems.Thm_NewtonianLipschitz_physicalNewtonianAcceleration_eq_smul
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_eq_formula
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3



set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) (x : Vec3) :
    c.accelerationField x =
      WithLp.ofLp
        (physicalNewtonianAcceleration c.gravitationalParameter
          (toPhysicalVec3 x)) := by
  rw [c.accelerationField_eq_formula x,
    physicalNewtonianAcceleration_eq_smul]
  rw [← euclideanRadius_eq_physical_norm]
  rw [WithLp.ofLp_smul, ofLp_toPhysicalVec3]
end NewtonianPointSource
end NewtonianLipschitz
