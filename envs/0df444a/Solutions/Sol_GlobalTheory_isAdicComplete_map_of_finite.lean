-- Prove2me | solution 1 for GlobalTheory.isAdicComplete_map_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:02:41.112573+00:00
-- url     : https://prove2.me/submissions/b36a91a6-0d04-49b7-a3af-ec13c02d42c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_isAdicComplete_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact isAdicComplete_of_finite I S
end GlobalTheory
