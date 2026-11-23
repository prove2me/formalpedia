-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.mem_level_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:46.26795+00:00
-- url     : https://prove2.me/submissions/bd592880-ca6d-48ff-9b71-6de90c72ec15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}
namespace GlobalTheory.CoeffSubring
theorem _root_.solution {n : ℕ} {x : S} (hx : x ∈ L) : x ∈ level p L n :=
  Subring.subset_closure (Or.inl (Or.inr hx))
end GlobalTheory.CoeffSubring
