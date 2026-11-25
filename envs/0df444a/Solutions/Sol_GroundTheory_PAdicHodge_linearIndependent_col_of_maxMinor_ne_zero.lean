-- Prove2me | solution 1 for GroundTheory.PAdicHodge.linearIndependent_col_of_maxMinor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:28.192128+00:00
-- url     : https://prove2.me/submissions/c5e14cce-5a27-4a9d-adec-383a83b3468b

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_GroundTheory_PAdicHodge_linearIndependent_col_iff_mulVec_eq_zero

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
theorem _root_.solution [IsDomain R] (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) (hs : maxMinor B s ≠ 0) : LinearIndependent R B.col := by
  rw [linearIndependent_col_iff_mulVec_eq_zero]
  intro v hv
  apply eq_zero_of_mulVec_eq_zero hs
  have : B.submatrix s.emb id *ᵥ v = fun i => (B *ᵥ v) (s.emb i) := by
    ext i; simp [mulVec, dotProduct]
  rw [this, hv]
  rfl
end GroundTheory.PAdicHodge
