-- Prove2me | solution 1 for GroundTheory.Global.coeff_map_C_mul_matrixGeomSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:57.915388+00:00
-- url     : https://prove2.me/submissions/5df7a175-d030-4df3-80bb-e5f580d533fe

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
theorem _root_.solution (M : Matrix n n R) (k : ℕ) (i j : n) :
    PowerSeries.coeff k ((M.map PowerSeries.C * matrixGeomSeries M) i j) = (M ^ (k + 1)) i j := by
  rw [pow_succ', Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [matrixGeomSeries, PowerSeries.coeff_C_mul]
end GroundTheory.Global
