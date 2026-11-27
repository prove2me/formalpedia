-- Prove2me | solution 1 for GroundTheory.PAdicHodge.compound_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:48:53.711804+00:00
-- url     : https://prove2.me/submissions/6bcbe682-d780-490b-8789-59b5ba60ab6d

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_GroundTheory_PAdicHodge_compound_apply

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
theorem _root_.solution {S : Type*} [CommRing S] (f : R →+* S) (P : Matrix (Fin m) (Fin n) R) :
    compound k (P.map f) = (compound k P).map f := by
  ext s t
  rw [compound_apply, map_apply, compound_apply, RingHom.map_det]
  rfl
end GroundTheory.PAdicHodge
