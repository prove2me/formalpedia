-- Prove2me | solution 1 for GlobalTheory.NB.BSet.lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:42.238407+00:00
-- url     : https://prove2.me/submissions/9824a486-2026-4e8c-bc11-0437b9b5d379

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
namespace BSet
theorem _root_.solution {up : ZMod n → Bool} {sz : ZMod n → ℕ} {b w Sn η m h : ℕ}
    (H : BSet F up sz b w Sn η m h) (i : ZMod n) : sz i < b ↔ sz i ≤ w := by
  have h1 := H.thick_or i
  have h2 := H.small.1
  have h3 := H.w_pos
  omega
end BSet
end GlobalTheory.NB
