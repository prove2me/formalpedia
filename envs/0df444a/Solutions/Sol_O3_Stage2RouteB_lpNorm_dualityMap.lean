-- Prove2me | solution 1 for O3.Stage2RouteB.lpNorm_dualityMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:25:32.828921+00:00
-- url     : https://prove2.me/submissions/b7d08ebe-99a5-458f-97f1-feaba8973bf7

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_conjugateExponent_ne_zero
import Theorems.Thm_O3_Stage2RouteB_lpPower_dualityMap
import Theorems.Thm_O3_lpNorm_nonneg


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    lpNorm (conjugateExponent p) (dualityMap p x) = lpNorm p x := by
  change (lpPower (conjugateExponent p) (dualityMap p x)) ^
      (1 / conjugateExponent p) = lpNorm p x
  rw [lpPower_dualityMap hp]
  have hn : 0 ≤ lpNorm p x := lpNorm_nonneg p x
  rw [← Real.rpow_mul hn]
  rw [show conjugateExponent p * (1 / conjugateExponent p) = 1 by
    field_simp [conjugateExponent_ne_zero hp]]
  rw [Real.rpow_one]
end O3.Stage2RouteB
