-- Prove2me | solution 1 for O3.Stage2RouteA.line_duality_pair_eq_affine_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:34:31.945485+00:00
-- url     : https://prove2.me/submissions/95eccd4d-4e3f-4fc4-b183-04b5aba499a2

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_pairing_dualityMap_smul
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



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {q : ℝ} (hq : 1 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h = 0) :
    (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h) =
      fun s : ℝ ↦ (s - t) * (lpNorm q h) ^ (2 : ℕ) := by
  funext s
  have hvec : x + s • h = (s - t) • h := by
    funext i
    have hzi := congrFun hz i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hzi ⊢
    linarith
  rw [hvec, pairing_dualityMap_smul hq]
end O3.Stage2RouteA
