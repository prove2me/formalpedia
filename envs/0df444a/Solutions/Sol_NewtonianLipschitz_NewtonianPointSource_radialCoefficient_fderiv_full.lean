-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.radialCoefficient_fderiv_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:38.874197+00:00
-- url     : https://prove2.me/submissions/6134af89-61af-475a-b197-ab52d398dee7

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
    (c : NewtonianPointSource) (x h : Vec3) (hx : x ≠ 0) :
    (fderiv ℝ c.radialCoefficient x) h =
      (3 * c.gravitationalParameter / euclideanRadius x ^ 5) *
        ⟪toPhysicalVec3 x, toPhysicalVec3 h⟫_ℝ := by
  let e : Vec3 ≃L[ℝ] PhysicalVec3 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hphys : e x ≠ 0 := by
    intro hz
    apply hx
    apply e.injective
    simpa only [map_zero] using hz
  have hr : ‖e x‖ ≠ 0 := norm_ne_zero_iff.mpr hphys
  let Q : Vec3 →L[ℝ] ℝ :=
    ((2 : ℕ) • (innerSL ℝ) (e x)).comp
      (e : Vec3 →L[ℝ] PhysicalVec3)
  have hsq :
      HasFDerivAt (fun y : Vec3 => ‖e y‖ ^ 2) Q x := by
    dsimp only [Q]
    exact ((hasStrictFDerivAt_norm_sq (e x)).hasFDerivAt).comp
      x e.hasFDerivAt
  have hroot :
      HasFDerivAt (fun y : Vec3 => ‖e y‖)
        ((1 / (2 * ‖e x‖)) • Q) x := by
    have hs := hsq.sqrt (pow_ne_zero 2 hr)
    have hfun :
        (fun y : Vec3 => Real.sqrt (‖e y‖ ^ 2)) =
          (fun y : Vec3 => ‖e y‖) := by
      funext y
      exact Real.sqrt_sq (norm_nonneg (e y))
    rw [hfun, Real.sqrt_sq (norm_nonneg (e x))] at hs
    exact hs
  have hpow :
      HasDerivAt (fun t : ℝ => t ^ 3)
        (3 * ‖e x‖ ^ 2) ‖e x‖ := by
    simpa using (hasDerivAt_pow 3 (‖e x‖))
  have hquot :
      HasDerivAt
        (fun t : ℝ => -(c.gravitationalParameter) / t ^ 3)
        (3 * c.gravitationalParameter / ‖e x‖ ^ 4) ‖e x‖ := by
    have h :=
      (hasDerivAt_const (‖e x‖) (-(c.gravitationalParameter))).div
        hpow (pow_ne_zero 3 hr)
    convert! h using 1 <;> field_simp [hr] <;> ring
  have hchain :=
    hquot.comp_hasFDerivAt x hroot
  have hrepr : c.radialCoefficient =
      (fun y : Vec3 => -(c.gravitationalParameter) / ‖e y‖ ^ 3) := by
    funext y
    change -(c.gravitationalParameter) / euclideanRadius y ^ 3 =
      -(c.gravitationalParameter) / ‖e y‖ ^ 3
    rw [euclideanRadius_eq_physical_norm,
      toPhysicalVec3_eq_continuousLinearEquiv]
  have hf :
      fderiv ℝ c.radialCoefficient x =
        (3 * c.gravitationalParameter / ‖e x‖ ^ 4) •
          ((1 / (2 * ‖e x‖)) • Q) := by
    rw [hrepr]
    simpa only [Function.comp_def] using hchain.fderiv
  rw [hf, euclideanRadius_eq_physical_norm]
  simp only [toPhysicalVec3_eq_continuousLinearEquiv]
  change (((3 * c.gravitationalParameter / ‖e x‖ ^ 4) •
      ((1 / (2 * ‖e x‖)) • Q)) h) =
    (3 * c.gravitationalParameter / ‖e x‖ ^ 5) *
      ⟪e x, e h⟫_ℝ
  simp only [Q, two_smul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    innerSL_apply_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe]
  field_simp [hr] <;> ring
end NewtonianPointSource
end NewtonianLipschitz
