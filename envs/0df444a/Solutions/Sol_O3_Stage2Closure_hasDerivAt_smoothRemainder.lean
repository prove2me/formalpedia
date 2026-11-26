-- Prove2me | solution 1 for O3.Stage2Closure.hasDerivAt_smoothRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:37.114461+00:00
-- url     : https://prove2.me/submissions/b212962b-6adb-45f4-b341-a06e7b984afa

import Definitions.Def_O3_Stage2RouteA
import Definitions.Def_O3_Stage2RouteB
import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_O3_Stage2BelowGeometry
import Theorems.Thm_O3_Stage2Closure_hasDerivAt_squaredLpEnergy_line
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
open O3
open O3.Stage2Closure
open scoped BigOperators
open Stage2RouteA Stage2RouteB
namespace O3.Stage2Closure
theorem _root_.solution {q : ℝ} (hq : 1 < q) {d : ℕ}
    (u h : Point d) (t : ℝ) :
    HasDerivAt (smoothRemainder q u h) (smoothRemainderDeriv q u h t) t := by
  have he := hasDerivAt_squaredLpEnergy_line hq u h t
  have hquad : HasDerivAt
      (fun s : ℝ ↦ ((q - 1) / 2) * s ^ (2 : ℕ) * (lpNorm q h) ^ (2 : ℕ))
      ((q - 1) * t * (lpNorm q h) ^ (2 : ℕ)) t := by
    have hraw := (((hasDerivAt_id t).pow 2).const_mul ((q - 1) / 2)).mul_const
      ((lpNorm q h) ^ (2 : ℕ))
    simp [id_eq] at hraw
    have heq : ((q - 1) / 2) * (2 * t) * (lpNorm q h) ^ (2 : ℕ) =
        (q - 1) * t * (lpNorm q h) ^ (2 : ℕ) := by ring
    rw [← heq]
    exact hraw
  exact he.sub hquad
end O3.Stage2Closure
