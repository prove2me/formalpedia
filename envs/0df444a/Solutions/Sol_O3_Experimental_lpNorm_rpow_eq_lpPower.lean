-- Prove2me | solution 1 for O3.Experimental.lpNorm_rpow_eq_lpPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:11.799598+00:00
-- url     : https://prove2.me/submissions/ebf4b09c-7138-4949-a1c7-6c37a56c4837

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
import Theorems.Thm_O3_lpPower_nonneg


set_option autoImplicit true
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p : ℝ} (hp : p ≠ 0) {d : ℕ} (z : Point d) :
    (lpNorm p z) ^ p = lpPower p z := by
  unfold lpNorm
  rw [one_div]
  exact Real.rpow_inv_rpow (lpPower_nonneg p z) hp
end O3.Experimental
