-- Prove2me | solution 1 for O3.pairing_sub_add_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:28.777402+00:00
-- url     : https://prove2.me/submissions/6aadf676-f6bf-46b0-836a-191c78848028

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
import Theorems.Thm_O3_stage9P_zero
import Theorems.Thm_O3_stage9P_succ
import Theorems.Thm_O3_lpNorm_two_sq_eq_pairing
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right


attribute [local simp] O3.stage9P_zero
attribute [local simp] O3.stage9P_succ

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d : ℕ} (x y : Vec d) :
    pairing (x - y) (x + y) =
      (lpNorm 2 x) ^ (2 : ℕ) - (lpNorm 2 y) ^ (2 : ℕ) := by
  rw [lpNorm_two_sq_eq_pairing, lpNorm_two_sq_eq_pairing]
  unfold pairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.add_apply]
  ring
end O3
