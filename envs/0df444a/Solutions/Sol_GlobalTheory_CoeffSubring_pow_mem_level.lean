-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.pow_mem_level
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:47.859998+00:00
-- url     : https://prove2.me/submissions/be27c9be-d953-4f01-a921-1a13c6dcd39e

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
theorem _root_.solution (n : ℕ) (x : S) : x ^ p ^ n ∈ level p L n :=
  Subring.subset_closure (Or.inl (Or.inl ⟨x, rfl⟩))
end GlobalTheory.CoeffSubring
