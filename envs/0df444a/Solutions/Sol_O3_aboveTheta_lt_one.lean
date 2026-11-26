-- Prove2me | solution 1 for O3.aboveTheta_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:04:50.672722+00:00
-- url     : https://prove2.me/submissions/cd335ac8-734f-4ea5-8b65-f90e1180c608

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveEta_pos
import Theorems.Thm_O3_aboveAP_lt_one
import Theorems.Thm_O3_aboveEta_lt_one
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
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : AboveTwoRegime p) :
    aboveTheta p < 1 := by
  rw [aboveTheta]
  calc
    aboveAP p * aboveEta p < 1 * aboveEta p :=
      mul_lt_mul_of_pos_right (aboveAP_lt_one hp) (aboveEta_pos p)
    _ < 1 := by simpa using aboveEta_lt_one hp
end O3
