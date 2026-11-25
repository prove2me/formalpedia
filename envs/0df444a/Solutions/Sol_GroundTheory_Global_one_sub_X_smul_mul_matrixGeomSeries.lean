-- Prove2me | solution 1 for GroundTheory.Global.one_sub_X_smul_mul_matrixGeomSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:33.258059+00:00
-- url     : https://prove2.me/submissions/5e87ecec-883f-4590-8aa2-9c325cfcb135

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Theorems.Thm_GroundTheory_Global_coeff_map_C_mul_matrixGeomSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GroundTheory GroundTheory.Global
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace GroundTheory.Global
theorem _root_.solution (M : Matrix n n R) :
    (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C) * matrixGeomSeries M = 1 := by
  ext i j k
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, map_sub]
  rcases k with _ | k
  · simp [matrixGeomSeries, Matrix.one_apply]
  · rw [PowerSeries.coeff_succ_X_mul, coeff_map_C_mul_matrixGeomSeries]
    by_cases h : i = j <;> simp [matrixGeomSeries, Matrix.one_apply, h]
end GroundTheory.Global
