-- Prove2me | solution 1 for O3.Experimental.powerDualityMap_strongMonotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:01:37.693925+00:00
-- url     : https://prove2.me/submissions/265c284c-1447-4907-a786-c7e35424ddbc

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
import Theorems.Thm_O3_Experimental_scalarJ_strongMonotone
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



set_option autoImplicit true
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p : ℝ} (hp : 2 < p) {d : ℕ}
    (u v : Point d) :
    (2 : ℝ) ^ (2 - p) * lpPower p (u - v) ≤
      pairing (powerDualityMap p u - powerDualityMap p v) (u - v) := by
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦
    scalarJ_strongMonotone (u := u i) (v := v i) hp
  simpa only [lpPower, pairing, powerDualityMap, scalarJ, Pi.sub_apply,
    Finset.mul_sum] using hsum
end O3.Experimental
