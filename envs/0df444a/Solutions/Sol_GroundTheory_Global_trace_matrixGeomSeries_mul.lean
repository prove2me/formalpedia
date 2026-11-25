-- Prove2me | solution 1 for GroundTheory.Global.trace_matrixGeomSeries_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:54.174384+00:00
-- url     : https://prove2.me/submissions/ccd236cb-1975-4ee0-82ff-b8ea3c90134c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly

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
    (matrixGeomSeries M * M.map PowerSeries.C).trace =
      PowerSeries.mk fun k => (M ^ (k + 1)).trace := by
  ext k
  rw [PowerSeries.coeff_mk, pow_succ, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [matrixGeomSeries, PowerSeries.coeff_mul_C]
end GroundTheory.Global
