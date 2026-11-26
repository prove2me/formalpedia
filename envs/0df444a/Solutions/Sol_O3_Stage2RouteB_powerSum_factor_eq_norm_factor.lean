-- Prove2me | solution 1 for O3.Stage2RouteB.powerSum_factor_eq_norm_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:34.481933+00:00
-- url     : https://prove2.me/submissions/618164a2-0bad-41ea-8246-8d16da423770

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_lpPower_pos_of_ne_zero


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 0 < p) {d : ℕ}
    {x : Point d} (hx : x ≠ 0) :
    (lpPower p x) ^ (2 / p - 1) = (lpNorm p x) ^ (2 - p) := by
  have hS : 0 < lpPower p x := lpPower_pos_of_ne_zero hx
  unfold lpNorm
  rw [← Real.rpow_mul hS.le]
  congr 1
  field_simp
end O3.Stage2RouteB
