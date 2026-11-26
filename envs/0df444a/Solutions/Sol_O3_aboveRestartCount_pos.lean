-- Prove2me | solution 1 for O3.aboveRestartCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:59.033996+00:00
-- url     : https://prove2.me/submissions/7c2d22b0-a832-48dd-b53b-b3c03269b887

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveAccumulatedWeight_zero
import Theorems.Thm_O3_aboveLevel_zero
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


attribute [local simp] O3.aboveAccumulatedWeight_zero
attribute [local simp] O3.aboveLevel_zero

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {Delta0 delta : ℝ}
    (hdelta : 0 < delta) (horder : delta < Delta0) :
    0 < aboveRestartCount Delta0 delta := by
  have hratio : 1 < Delta0 / delta := (lt_div_iff₀ hdelta).2 (by simpa)
  have hlog : 0 < Real.logb 2 (Delta0 / delta) :=
    Real.logb_pos (by norm_num) hratio
  exact Nat.ceil_pos.mpr hlog
end O3
