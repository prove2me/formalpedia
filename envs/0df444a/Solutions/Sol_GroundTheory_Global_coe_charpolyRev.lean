-- Prove2me | solution 1 for GroundTheory.Global.coe_charpolyRev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:08.096702+00:00
-- url     : https://prove2.me/submissions/ad6fe329-49c7-4cd1-90be-9e3c1a80001e

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
    ((M.charpolyRev : R[X]) : PowerSeries R) =
      (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C).det := by
  rw [Matrix.charpolyRev, ← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;>
    simp [h, Polynomial.coeToPowerSeries.ringHom_apply] <;> ring
end GroundTheory.Global
