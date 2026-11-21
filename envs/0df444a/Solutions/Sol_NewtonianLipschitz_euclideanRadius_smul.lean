-- Prove2me | solution 1 for NewtonianLipschitz.euclideanRadius_smul
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:39:43.917892+00:00
-- url     : https://prove2.me/submissions/1eb83e60-0905-4b99-a990-6fff012dc6cc

module
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz


theorem solution (c : ℝ) (x : Vec3) :
    euclideanRadius (c • x) = |c| * euclideanRadius x := by
  unfold euclideanRadius
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (c * x 0) ^ 2 + (c * x 1) ^ 2 + (c * x 2) ^ 2 =
      c ^ 2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) by ring]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
