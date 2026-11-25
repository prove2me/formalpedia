-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_maxMinor_ne_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:40.583798+00:00
-- url     : https://prove2.me/submissions/a0d30684-df90-4a87-b27b-7327bcd1c1ae

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_maxMinor_ne_zero_of_linearIndependent_alt_969c684934e8


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
variable {n k : ℕ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution [IsDomain R]
    (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 :=
  _root_.GroundTheory.Variant₂.N1.exists_maxMinor_ne_zero_of_linearIndependent_alt B hB
end GroundTheory.PAdicHodge
