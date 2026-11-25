-- Prove2me | solution 1 for LovaszTheta.indepNum_strongPow_cycle_five_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:19:25.670436+00:00
-- url     : https://prove2.me/submissions/bb99d892-82c7-4196-ac82-6ee47398fc70

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_le
public import Theorems.Thm_LovaszTheta_umbH_sq
public import Theorems.Thm_LovaszTheta_umbrella_isOrthonormalRep

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution (k : ℕ) :
    ((strongPow (cycleGraph 5) k).indepNum : ℝ) ≤ Real.sqrt 5 ^ k := by
  refine indepNum_strongPow_le (cycleGraph 5) umbrella_isOrthonormalRep (c := ![0, 0, 1])
    (by simp [dotProduct, Fin.sum_univ_three]) (Real.sqrt_nonneg 5) (fun i => ?_) k
  have : dotProduct ![0, 0, 1] (umbrella i) = umbH := by
    simp [dotProduct, Fin.sum_univ_three, umbrella]
  rw [this, umbH_sq]
  have hpos : 0 < Real.sqrt 5 := by positivity
  rw [mul_one_div_cancel hpos.ne']
end LovaszTheta
