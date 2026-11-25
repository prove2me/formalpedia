-- Prove2me | solution 1 for GlobalTheory.NB.typed_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:15:31.840737+00:00
-- url     : https://prove2.me/submissions/2eb36601-7e58-4fc3-afcb-3a2f78537d88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
variable {l : ℕ} {O : Type} [CommRing O] [IsDomain O] {R : Fr l O} {n r₁ r : ℕ}
variable {S₁ : Sys R n r₁} {S : Sys R n r} {F : Hom S₁ S}
namespace GlobalTheory.NB
theorem _root_.solution {up : ZMod n → Fin R.e → Bool} {b : ZMod n → Fin R.e → ℕ} {Sn η m h : ℕ} :
    Typed F up b Sn η m h ↔
      TypedOnto F up b Sn η m h ∧ ∀ i, ∃ a : ℕ, F.Kills i ((l : O⟦X⟧) ^ a) :=
  ⟨fun H => ⟨⟨H.good.1, H.jumps, H.size, H.le_h, H.low⟩, H.good.2⟩,
    fun H => ⟨⟨H.1.onto, H.2⟩, H.1.jumps, H.1.size, H.1.le_h, H.1.low⟩⟩
end GlobalTheory.NB
