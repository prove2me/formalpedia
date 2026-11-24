-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.norm_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:26:43.019651+00:00
-- url     : https://prove2.me/submissions/8129cc83-9565-4242-befb-baa0861c4a80

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_herm_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_herm_smul_left

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
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
variable {δ : L} {e f : V}
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution (hs : IsInv s) (hh : IsHerm s h) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (a b : L) {w : V} (hew : h e w = 0) (hfw : h f w = 0) :
    h (a • e + b • f + w) (a • e + b • f + w) = δ * (s a * b) + s (δ * (s a * b)) + h w w := by
  have hfe := h_fe hh hef
  have hwe : h w e = 0 := by rw [hh.2.2.1 e w, hew, map_zero]
  have hwf : h w f = 0 := by rw [hh.2.2.1 f w, hfw, map_zero]
  simp only [herm_add_left hh, hh.1, herm_smul_left hh, hh.2.1, he, hf, hef, hfe, hew, hfw, hwe,
    hwf, mul_zero, zero_add, add_zero, map_mul, hs.1]
  ring
end GlobalTheory.CompanionTheory.RgSplit
