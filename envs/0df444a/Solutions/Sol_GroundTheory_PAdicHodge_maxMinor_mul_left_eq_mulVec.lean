-- Prove2me | solution 1 for GroundTheory.PAdicHodge.maxMinor_mul_left_eq_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:56.111172+00:00
-- url     : https://prove2.me/submissions/8f748ba0-17c2-4d71-a0db-63d52f346296

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_GroundTheory_PAdicHodge_maxMinor_mul_left

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
theorem _root_.solution (P : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    maxMinor (P * B) = compound k P *ᵥ maxMinor B := by
  funext s
  rw [maxMinor_mul_left]
  rfl
end GroundTheory.PAdicHodge
