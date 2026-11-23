-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.mem_level_of_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:10.573723+00:00
-- url     : https://prove2.me/submissions/0155bc99-a63f-4353-9822-f1d1dd6a295b

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
theorem _root_.solution {n : ℕ} {x : S} (hx : x ∈ maximalIdeal S ^ (n + 1)) :
    x ∈ level p L n :=
  Subring.subset_closure (Or.inr hx)
end GlobalTheory.CoeffSubring
