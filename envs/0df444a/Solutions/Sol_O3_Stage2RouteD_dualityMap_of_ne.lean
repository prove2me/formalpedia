-- Prove2me | solution 1 for O3.Stage2RouteD.dualityMap_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:35.310971+00:00
-- url     : https://prove2.me/submissions/c19d316e-9dd7-4d1c-a492-d3d41f14a18a

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_eq_zero_iff
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right


attribute [local simp] O3.Stage2RouteD.dualityMap_zero

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD
namespace O3.Stage2RouteD
theorem _root_.solution {p : ℝ} (hp : 0 < p) {d : ℕ} {u : Point d}
    (hu : u ≠ 0) :
    dualityMap p u = fun i ↦ (lpNorm p u) ^ (2 - p) *
      (|u i| ^ (p - 2) * u i) := by
  simp [dualityMap, (lpNorm_eq_zero_iff hp).not.mpr hu]
end O3.Stage2RouteD
