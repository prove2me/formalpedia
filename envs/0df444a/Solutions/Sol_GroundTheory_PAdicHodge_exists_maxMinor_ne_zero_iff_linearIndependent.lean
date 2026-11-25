-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_maxMinor_ne_zero_iff_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:03.487139+00:00
-- url     : https://prove2.me/submissions/181f304c-cb5a-4197-95be-a0dadce1fcfc

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_GroundTheory_PAdicHodge_linearIndependent_col_of_maxMinor_ne_zero
import Theorems.Thm_GroundTheory_PAdicHodge_exists_maxMinor_ne_zero_of_linearIndependent

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
    (B : Matrix (Fin n) (Fin k) R) :
    (∃ s : KSubset n k, maxMinor B s ≠ 0) ↔ LinearIndependent R B.col :=
  ⟨fun ⟨s, hs⟩ => linearIndependent_col_of_maxMinor_ne_zero B s hs,
    exists_maxMinor_ne_zero_of_linearIndependent B⟩
end GroundTheory.PAdicHodge
