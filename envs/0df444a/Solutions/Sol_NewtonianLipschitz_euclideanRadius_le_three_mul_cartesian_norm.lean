-- Prove2me | solution 1 for NewtonianLipschitz.euclideanRadius_le_three_mul_cartesian_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:37.104676+00:00
-- url     : https://prove2.me/submissions/0d38335c-8104-405b-8906-831898ba28bc

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
public import Theorems.Thm_NewtonianLipschitz_euclideanRadius_eq_coordinates
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
theorem _root_.solution (x : Vec3) :
    euclideanRadius x ≤ 3 * ‖x‖ := by
  have h0 : (x 0) ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (pow_le_pow_left₀ (norm_nonneg (x 0))
        (norm_le_pi_norm x 0) 2)
  have h1 : (x 1) ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (pow_le_pow_left₀ (norm_nonneg (x 1))
        (norm_le_pi_norm x 1) 2)
  have h2 : (x 2) ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (pow_le_pow_left₀ (norm_nonneg (x 2))
        (norm_le_pi_norm x 2) 2)
  rw [euclideanRadius_eq_coordinates]
  apply (Real.sqrt_le_left (by positivity : 0 ≤ (3 : ℝ) * ‖x‖)).2
  nlinarith [sq_nonneg (‖x‖)]
end NewtonianLipschitz
