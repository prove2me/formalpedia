-- Prove2me | solution 1 for GlobalTheory.NB.CokBound.of_kills_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:45.54469+00:00
-- url     : https://prove2.me/submissions/8c6c79ad-5efb-44f0-8780-1b2333e64864

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
namespace CokBound
theorem _root_.solution (h : ∀ i, F.Kills i 1) (Hw : ZMod n → ℕ) (H : ℕ) :
    CokBound F Hw H :=
  ⟨fun _ => 0, fun _ => Nat.zero_le _, fun _ => by simp only [Nat.cast_zero, zero_div]; positivity,
    fun i => (h i).of_dvd (one_dvd _), fun i => (h i).of_dvd (one_dvd _)⟩
end CokBound
end GlobalTheory.NB
