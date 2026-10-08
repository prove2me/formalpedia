-- Prove2me | solution 1 for MethanolMuDrift.rotational_sensitivity_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:47:09.658983+00:00
-- url     : https://prove2.me/submissions/6caac286-7e47-4072-bed3-6664b8b1e62e

import Mathlib
import Definitions.Def_Bagdonaite2013_MethanolMuDrift

open MethanolMuDrift in
theorem solution (C μ : ℝ) (hC : C ≠ 0) (hμ : 0 < μ) :
    sensitivityCoeff (fun m => C / m) μ = -1 := by
  have hμ0 : μ ≠ 0 := hμ.ne'
  have hfun : (fun m : ℝ => C / m) = fun y => C * y⁻¹ := by
    funext y; rw [div_eq_mul_inv]
  have h : HasDerivAt (fun y : ℝ => C * y⁻¹) (C * -(μ ^ 2)⁻¹) μ :=
    (hasDerivAt_inv hμ0).const_mul C
  unfold sensitivityCoeff
  rw [hfun, h.deriv]
  field_simp
