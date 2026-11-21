-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.accelerationField_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:17.537808+00:00
-- url     : https://prove2.me/submissions/f0a48b76-8fd7-42ae-ab91-abd5314ca37a

module
public import Definitions.Def_NewtonianLipschitz_Field
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Theorems.Thm_NewtonianLipschitz_physicalNewtonianAcceleration_contDiffAt
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_accelerationField_eq_physical
public import Theorems.Thm_NewtonianLipschitz_ofLp_toPhysicalVec3
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_apply
public import Theorems.Thm_NewtonianLipschitz_toPhysicalVec3_eq_continuousLinearEquiv
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
    (c : NewtonianPointSource) (x : Vec3) (hx : x ≠ 0) :
    ContDiffAt ℝ 1 c.accelerationField x := by
  let e : Vec3 ≃L[ℝ] PhysicalVec3 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hn : e x ≠ 0 := by
    intro hzero
    apply hx
    apply e.injective
    simpa only [map_zero] using hzero
  have hphys : ContDiffAt ℝ 1
      (physicalNewtonianAcceleration c.gravitationalParameter) (e x) :=
    physicalNewtonianAcceleration_contDiffAt
      c.gravitationalParameter (e x) hn
  have hcomp : ContDiffAt ℝ 1
      (fun y : Vec3 =>
        e.symm (physicalNewtonianAcceleration
          c.gravitationalParameter (e y))) x :=
    (e.symm.contDiff.contDiffAt).comp x
      (hphys.comp x e.contDiff.contDiffAt)
  have hfield : c.accelerationField =
      (fun y : Vec3 =>
        e.symm (physicalNewtonianAcceleration
          c.gravitationalParameter (e y))) := by
    funext y
    rw [c.accelerationField_eq_physical y,
      toPhysicalVec3_eq_continuousLinearEquiv]
    rfl
  rw [hfield]
  exact hcomp
end NewtonianPointSource
end NewtonianLipschitz
