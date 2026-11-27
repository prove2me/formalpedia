-- Prove2me | solution 1 for GroundTheory.PAdicHodge.maxMinor_ne_zero_iff_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:46.470674+00:00
-- url     : https://prove2.me/submissions/c19bdde9-ef09-49df-a132-4be50f0c5e57

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_GroundTheory_PAdicHodge_exists_maxMinor_ne_zero_iff_linearIndependent

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
theorem _root_.solution [IsDomain R] (B : Matrix (Fin n) (Fin k) R) :
    maxMinor B ≠ 0 ↔ LinearIndependent R B.col := by
  rw [← exists_maxMinor_ne_zero_iff_linearIndependent, Ne, funext_iff, not_forall]
  rfl
end GroundTheory.PAdicHodge
