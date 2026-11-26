-- Prove2me | solution 1 for O3.Stage2RouteB.lpPower_pos_of_point_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:03.374595+00:00
-- url     : https://prove2.me/submissions/28ffad08-702c-41b6-be7e-67ecafe004ac

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_lpPower_pos_of_ne_zero


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} {d : ℕ} {x : Point d}
    (hx : x ≠ 0) : 0 < lpPower p x :=
  lpPower_pos_of_ne_zero hx
end O3.Stage2RouteB
