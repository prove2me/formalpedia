-- Prove2me | solution 1 for GroundTheory.PAdicHodge.maxMinor_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:01.904326+00:00
-- url     : https://prove2.me/submissions/453f78a5-bad1-4eaa-a9af-68a1ec29abe9

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
theorem _root_.solution {S : Type*} [CommRing S] (f : R →+* S) (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) : maxMinor (B.map f) s = f (maxMinor B s) := by
  unfold maxMinor
  rw [RingHom.map_det]
  rfl
end GroundTheory.PAdicHodge
