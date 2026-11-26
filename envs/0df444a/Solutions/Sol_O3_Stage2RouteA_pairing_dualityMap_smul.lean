-- Prove2me | solution 1 for O3.Stage2RouteA.pairing_dualityMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:36.104981+00:00
-- url     : https://prove2.me/submissions/f00a0a23-1e2f-4212-938a-e90ee0892ef2

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteC_lpNorm_smul
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_Stage2RouteD_pairing_dualityMap_self
import Theorems.Thm_O3_Stage2RouteD_pairing_smul_right
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



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {q : ℝ} (hq : 1 < q) {d : ℕ}
    (a : ℝ) (h : Point d) :
    pairing (dualityMap q (a • h)) h =
      a * (lpNorm q h) ^ (2 : ℕ) := by
  by_cases ha : a = 0
  · subst a
    simp [O3.Stage2RouteD.dualityMap_zero (by linarith : 0 < q), pairing]
  · have hself := O3.Stage2RouteD.pairing_dualityMap_self hq (a • h)
    rw [O3.Stage2RouteD.pairing_smul_right,
      O3.Stage2RouteC.lpNorm_smul (by linarith : 1 ≤ q)] at hself
    have habs : |a| ^ (2 : ℕ) = a ^ (2 : ℕ) := sq_abs a
    rw [mul_pow, habs] at hself
    apply (mul_left_cancel₀ ha)
    calc
      a * pairing (dualityMap q (a • h)) h =
          a ^ (2 : ℕ) * (lpNorm q h) ^ (2 : ℕ) := hself
      _ = a * (a * (lpNorm q h) ^ (2 : ℕ)) := by ring
end O3.Stage2RouteA
