-- Prove2me | solution 1 for GlobalTheory.NB.Hom.Kills.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:15:26.263769+00:00
-- url     : https://prove2.me/submissions/640a4e39-50cb-41f1-8271-f283182eadce

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
omit [IsDomain O]
namespace GlobalTheory.NB
namespace Hom.Kills
theorem _root_.solution {i : ZMod n} {f g : O⟦X⟧} (h : F.Kills i f) (hfg : f ∣ g) :
    F.Kills i g := by
  obtain ⟨c, rfl⟩ := hfg
  intro y hy
  obtain ⟨x, hx, e⟩ := h (c • y) (Submodule.smul_mem _ _ hy)
  exact ⟨x, hx, by rw [e, smul_smul]⟩
end Hom.Kills
end GlobalTheory.NB
