-- Prove2me | solution 1 for O3.Stage2RouteA.lpPower_rpow_two_div_sub_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:25.853811+00:00
-- url     : https://prove2.me/submissions/f62b7387-73da-482d-8be4-9e12209048f6

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_lpPower_pos_of_ne_zero


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p : ℝ} (hp : p ≠ 0) {d : ℕ}
    {z : Point d} (hz : z ≠ 0) :
    (lpPower p z) ^ (2 / p - 1) = (lpNorm p z) ^ (2 - p) := by
  have hS : 0 < lpPower p z := lpPower_pos_of_ne_zero hz
  unfold lpNorm
  rw [← Real.rpow_mul hS.le]
  congr 1
  field_simp
end O3.Stage2RouteA
