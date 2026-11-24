-- Prove2me | solution 1 for GlobalTheory.UnramSub.mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:24.934438+00:00
-- url     : https://prove2.me/submissions/4656c0dd-7154-405e-a15d-d97c5534ca01

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
theorem _root_.solution {T : Subring F} (h : UnramSub i T) (v : V) : i v ∈ T := by
  obtain ⟨_, f, hf, -⟩ := h
  exact hf v ▸ (f v).2
end GlobalTheory.UnramSub
