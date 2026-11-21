-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.radialCoefficient_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:19.867097+00:00
-- url     : https://prove2.me/submissions/7fbef26e-8bfc-4ef6-94cc-fd7a50021173

module
public import Definitions.Def_NewtonianLipschitz_Smoothness
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Derivative
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_physical_norm
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
    ContDiffAt ℝ 1 c.radialCoefficient x := by
  let e : Vec3 ≃L[ℝ] PhysicalVec3 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hphys : e x ≠ 0 := by
    intro hz
    apply hx
    apply e.injective
    simpa only [map_zero] using hz
  have hnorm : ContDiffAt ℝ 1 (fun y : Vec3 => ‖e y‖) x := by
    exact (contDiffAt_norm ℝ hphys).comp x e.contDiff.contDiffAt
  have hpow : ContDiffAt ℝ 1 (fun y : Vec3 => ‖e y‖ ^ 3) x :=
    hnorm.pow 3
  have hpow_ne : ‖e x‖ ^ 3 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hphys)
  have hscalar : ContDiffAt ℝ 1
      (fun y : Vec3 => -(c.gravitationalParameter) / ‖e y‖ ^ 3) x :=
    contDiffAt_const.div hpow hpow_ne
  have hrepr : c.radialCoefficient =
      (fun y : Vec3 => -(c.gravitationalParameter) / ‖e y‖ ^ 3) := by
    funext y
    change -(c.gravitationalParameter) / euclideanRadius y ^ 3 =
      -(c.gravitationalParameter) / ‖e y‖ ^ 3
    rw [euclideanRadius_eq_physical_norm,
      toPhysicalVec3_eq_continuousLinearEquiv]
  rw [hrepr]
  exact hscalar
end NewtonianPointSource
end NewtonianLipschitz
