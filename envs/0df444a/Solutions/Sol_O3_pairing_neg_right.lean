-- Prove2me | solution 1 for O3.pairing_neg_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:58.353923+00:00
-- url     : https://prove2.me/submissions/e9ea366f-c01d-4b13-a7a9-9bb96085f503

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_pairing_neg_left
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.pairing_neg_left

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d : ℕ} (x y : Point d) :
    pairing x (-y) = -pairing x y := by
  simp [pairing]
end O3
