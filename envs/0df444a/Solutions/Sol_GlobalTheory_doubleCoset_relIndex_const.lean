-- Prove2me | solution 1 for GlobalTheory.doubleCoset_relIndex_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:03.971728+00:00
-- url     : https://prove2.me/submissions/6f12edf9-888a-400c-8d22-01def577d345

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst
import Theorems.Thm_GlobalTheory_DoubleCosetWeight_relIndex_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace GlobalTheory
theorem _root_.solution : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C :=
  fun G _ T C K hC => GlobalTheory.DoubleCosetWeight.relIndex_eq T C K hC
end GlobalTheory
