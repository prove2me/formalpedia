-- Prove2me | solution 1 for GlobalTheory.NB.Hom.Kills.pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:49.070282+00:00
-- url     : https://prove2.me/submissions/c059f85d-eab9-484e-b0da-c4e98b52c9e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne
import Theorems.Thm_GlobalTheory_NB_Hom_Kills_of_dvd

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
omit [IsDomain O]
namespace GlobalTheory.NB
namespace Hom.Kills
theorem _root_.solution {i : ZMod n} {f : O⟦X⟧} {a a' : ℕ} (h : F.Kills i (f ^ a)) (ha : a ≤ a') :
    F.Kills i (f ^ a') := h.of_dvd (pow_dvd_pow f ha)
end Hom.Kills
end GlobalTheory.NB
