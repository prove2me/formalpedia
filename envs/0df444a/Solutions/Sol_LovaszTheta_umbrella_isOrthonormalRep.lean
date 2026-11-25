-- Prove2me | solution 1 for LovaszTheta.umbrella_isOrthonormalRep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:07:38.682497+00:00
-- url     : https://prove2.me/submissions/a073aa7f-bb33-44e7-9aa7-91fc4ac45615

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Theorems.Thm_LovaszTheta_cos_pentAngle_sub
public import Theorems.Thm_LovaszTheta_umbH_sq
public import Theorems.Thm_LovaszTheta_umbS_sq
public import Theorems.Thm_LovaszTheta_umbrella_dot

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution : IsOrthonormalRep (cycleGraph 5) umbrella := by
  refine ⟨fun i => ?_, fun i j hij hadj => ?_⟩
  · rw [umbrella_dot, sub_self, Real.cos_zero, umbS_sq, umbH_sq]; ring
  · rw [umbrella_dot, cos_pentAngle_sub i j hij hadj, umbS_sq, umbH_sq]
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hpos : 0 < Real.sqrt 5 := by positivity
    field_simp
    nlinarith [h5]
end LovaszTheta
