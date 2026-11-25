-- Prove2me | solution 1 for LovaszTheta.pentAngle_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:46:59.700893+00:00
-- url     : https://prove2.me/submissions/f4e804da-89cc-4a55-aef2-ddb835aa775d

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution (i j : Fin 5) (hij : i ≠ j) (hadj : ¬ (cycleGraph 5).Adj i j) :
    pentAngle i - pentAngle j = 4 * Real.pi / 5 ∨
    pentAngle i - pentAngle j = -(4 * Real.pi / 5) ∨
    pentAngle i - pentAngle j = 6 * Real.pi / 5 ∨
    pentAngle i - pentAngle j = -(6 * Real.pi / 5) := by
  replace hadj : ¬ (i - j = 1 ∨ j - i = 1) := fun h => hadj ((cycleGraph_adj (n := 3)).mpr h)
  fin_cases i <;> fin_cases j <;>
    first
    | (exfalso; revert hij hadj; decide)
    | (left; norm_num [pentAngle]; ring1)
    | (right; left; norm_num [pentAngle] ; ring1)
    | (right; right; left; norm_num [pentAngle] ; ring1)
    | (right; right; right; norm_num [pentAngle] ; ring1)
end LovaszTheta
