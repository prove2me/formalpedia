-- Prove2me | solution 1 for O3.Stage2RouteD.weightedHolder_upper_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:40.9992+00:00
-- url     : https://prove2.me/submissions/1ac6a18a-abd7-4ad7-a81c-636297b28b8e

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_Stage2RouteD_weightedHolder_upper
import Theorems.Thm_O3_Stage2RouteD_lpPower_factor_eq_lpNorm

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {q : ℝ} (hq : 2 < q) {d : ℕ}
    (z h : Point d) (hz : z ≠ 0) :
    (lpPower q z) ^ (2 / q - 1) *
        (∑ i, |z i| ^ (q - 2) * (h i) ^ (2 : ℕ)) ≤
      (lpNorm q h) ^ (2 : ℕ) := by
  rw [lpPower_factor_eq_lpNorm (by linarith : 0 < q) hz]
  exact weightedHolder_upper hq z h hz
end O3.Stage2RouteD
