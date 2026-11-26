-- Prove2me | solution 1 for O3.Stage2RouteB.abs_dualityMap_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:59.546826+00:00
-- url     : https://prove2.me/submissions/0cbc3974-37ba-4878-ac4e-d48aeafcf4f1

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_abs_powerDuality_coordinate
import Theorems.Thm_O3_lpNorm_pos_of_ne_zero


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ}
    {x : Point d} (hx : x ≠ 0) (i : Fin d) :
    |dualityMap p x i| =
      (lpNorm p x) ^ (2 - p) * |x i| ^ (p - 1) := by
  have hn : 0 < lpNorm p x := lpNorm_pos_of_ne_zero hx
  rw [dualityMap, if_neg hn.ne']
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hn.le _),
    abs_powerDuality_coordinate hp]
end O3.Stage2RouteB
