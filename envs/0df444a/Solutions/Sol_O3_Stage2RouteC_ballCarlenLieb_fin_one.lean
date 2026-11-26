-- Prove2me | solution 1 for O3.Stage2RouteC.ballCarlenLieb_fin_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:56.37817+00:00
-- url     : https://prove2.me/submissions/724d2e6a-4f7f-454d-9447-f560fe9abfc4

import Definitions.Def_O3_Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Definitions.Def_O3_Stage2RouteC
import Theorems.Thm_O3_Stage2RouteC_lpNorm_fin_one
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
open O3 O3.Stage2RouteC
namespace O3.Stage2RouteC
theorem _root_.solution {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (u v : O3.Point 1) :
    (O3.lpNorm p (u + v)) ^ (2 : ℕ) +
        (p - 1) * (O3.lpNorm p (u - v)) ^ (2 : ℕ) ≤
      2 * ((O3.lpNorm p u) ^ (2 : ℕ) + (O3.lpNorm p v) ^ (2 : ℕ)) := by
  simp_rw [lpNorm_fin_one (zero_lt_one.trans hp)]
  simp only [Pi.add_apply, Pi.sub_apply, sq_abs]
  nlinarith [sq_nonneg (u 0 - v 0)]
end O3.Stage2RouteC
