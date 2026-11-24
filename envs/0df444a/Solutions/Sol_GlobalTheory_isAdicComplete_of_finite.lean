-- Prove2me | solution 1 for GlobalTheory.isAdicComplete_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:13.002723+00:00
-- url     : https://prove2.me/submissions/163a77fb-14e1-4fad-94b4-ec33bdf6f942

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_isPrecomplete_of_finite

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
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M where
  toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  toIsPrecomplete := isPrecomplete_of_finite I M
end GlobalTheory
