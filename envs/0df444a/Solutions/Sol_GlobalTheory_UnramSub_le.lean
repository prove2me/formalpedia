-- Prove2me | solution 1 for GlobalTheory.UnramSub.le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:56.56948+00:00
-- url     : https://prove2.me/submissions/e0f88381-ad9d-4559-b5e0-eac828f56c0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramSub
import Theorems.Thm_GlobalTheory_UnramSub_mem

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
theorem _root_.solution {T₁ T₂ : Subring F} (h₂ : UnramSub T₁.subtype T₂) : T₁ ≤ T₂ := fun z hz => h₂.mem ⟨z, hz⟩
end GlobalTheory.UnramSub
