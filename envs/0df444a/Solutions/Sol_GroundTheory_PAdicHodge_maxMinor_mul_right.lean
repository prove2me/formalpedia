-- Prove2me | solution 1 for GroundTheory.PAdicHodge.maxMinor_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:02.571571+00:00
-- url     : https://prove2.me/submissions/574ad90b-1e8f-428e-900f-89bc385dbd25

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Matrix Finset Equiv
variable {R : Type*} [CommRing R]
variable {m n k : ℕ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (B : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R)
    (s : KSubset n k) : maxMinor (B * C) s = maxMinor B s * C.det := by
  unfold maxMinor
  rw [← det_mul]
  congr 1
end GroundTheory.PAdicHodge
