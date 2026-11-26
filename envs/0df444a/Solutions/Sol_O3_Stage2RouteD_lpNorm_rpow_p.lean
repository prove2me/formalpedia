-- Prove2me | solution 1 for O3.Stage2RouteD.lpNorm_rpow_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:08.251572+00:00
-- url     : https://prove2.me/submissions/107622f6-7950-4c41-bc33-51b0f3608175

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_Experimental_lpNorm_rpow_eq_lpPower


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ} (u : Point d) :
    (lpNorm p u) ^ p = lpPower p u := by
  exact O3.Experimental.lpNorm_rpow_eq_lpPower (by linarith) u
end O3.Stage2RouteD
