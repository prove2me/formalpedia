-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.exactDifferentialAcceleration_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:02:25.074724+00:00
-- url     : https://prove2.me/submissions/d34de6fd-151a-4f76-889c-e4d8fc0136a0

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Field
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_zero
attribute [local simp] NewtonianLipschitz.ofLp_toPhysicalVec3
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_apply
attribute [local simp] NewtonianLipschitz.toPhysicalVec3_zero



set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution
    (c : NewtonianPointSource) :
    c.exactDifferentialAcceleration 0 = 0 := by
  simp only [NewtonianPointSource.exactDifferentialAcceleration,
    add_zero, sub_self]
end NewtonianPointSource
end NewtonianLipschitz
