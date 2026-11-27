-- Prove2me | solution 2 for GlobalTheory.UnramSub.isDVR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:52.30125+00:00
-- url     : https://prove2.me/submissions/bd3ffcfb-83a7-4cf0-a4fa-bed6f09b9e0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.UnramSub
variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}
namespace GlobalTheory.UnramSub
theorem _root_.solution {T : Subring F} (h : UnramSub i T) : IsDiscreteValuationRing T := h.1
end GlobalTheory.UnramSub
