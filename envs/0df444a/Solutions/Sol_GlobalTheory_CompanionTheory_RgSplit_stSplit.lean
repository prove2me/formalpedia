-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.stSplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:06:47.637597+00:00
-- url     : https://prove2.me/submissions/ee0cbc6f-3288-460b-af3e-408efaedefeb

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_decomp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_herm_restrict
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_restrict_isMax
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_split_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution : StSandwich → StPairing → StSplit := by
  intro hS hP L _ _ _ _ s hs δ hδ V _ _ _ h hh e f U he hf hef hU
  have hδ0 := hδ.1
  refine ⟨herm_restrict hh hδ0 he hf hef hU, fun x => ⟨_, _, _, (hU _).2
    (pr_orth hh hδ0 he hf hef x), decomp hh δ e f x⟩, ?_, fun Λ hΛ heΛ hfΛ => ?_⟩
  · rintro rfl
    exact hδ0 (hef ▸ ((hU f).1 Submodule.mem_top).1)
  · have hpair := (hP L s hs δ hδ V h hh Λ hΛ).1
    refine ⟨restrict_isMax hS hs hδ hh he hf hef hU hΛ hpair heΛ hfΛ, fun a b w hw => ?_⟩
    have hw' := (hU w).1 hw
    exact split_mem_iff hs hδ0 hh he hf hef hΛ.1 hpair heΛ hfΛ a b hw'.1 hw'.2
end GlobalTheory.CompanionTheory.RgSplit
