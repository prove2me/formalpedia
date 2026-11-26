-- Prove2me | solution 1 for O3.Stage2RouteB.fenchelYoung_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:55.411003+00:00
-- url     : https://prove2.me/submissions/e94de9a9-4950-4feb-854c-38450778a5b7

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_squaredLpEnergy_eq_quadraticRegularizer
import Theorems.Thm_O3_holderConjugate_conjugateExponent
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_one_lt_conjugateExponent
import Theorems.Thm_O3_pairing_le_lpNorm_mul
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
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ} (w y : Point d) :
    pairing w y - squaredLpEnergy (conjugateExponent p) w ≤ squaredLpEnergy p y := by
  have hpair := pairing_le_lpNorm_mul (holderConjugate_conjugateExponent hp).symm w y
  rw [squaredLpEnergy_eq_quadraticRegularizer
    (lt_trans zero_lt_one (one_lt_conjugateExponent hp))]
  rw [squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p)]
  simp only [quadraticRegularizer, sub_zero]
  have hsq := sq_nonneg (lpNorm (conjugateExponent p) w - lpNorm p y)
  nlinarith
end O3.Stage2RouteB
