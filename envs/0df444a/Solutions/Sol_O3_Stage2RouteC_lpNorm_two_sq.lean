-- Prove2me | solution 1 for O3.Stage2RouteC.lpNorm_two_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:52.5288+00:00
-- url     : https://prove2.me/submissions/238dcc72-2ec5-4582-aa29-8cc3c57fe7cb

import Definitions.Def_O3_Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Definitions.Def_O3_Stage2RouteC
import Theorems.Thm_O3_Stage2RouteC_lpNorm_eq_piLpNorm
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
theorem _root_.solution {d : ℕ} (x : O3.Point d) :
    (O3.lpNorm 2 x) ^ (2 : ℕ) = ∑ i, (x i) ^ (2 : ℕ) := by
  rw [lpNorm_eq_piLpNorm (p := (2 : ℝ)) (by norm_num)]
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [htwo]
  change ‖(WithLp.toLp 2 x : PiLp 2 (fun _ : Fin d ↦ ℝ))‖ ^ (2 : ℕ) =
    ∑ i, (x i) ^ (2 : ℕ)
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]
end O3.Stage2RouteC
