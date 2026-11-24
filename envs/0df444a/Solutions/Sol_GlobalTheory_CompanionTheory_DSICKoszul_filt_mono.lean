-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.filt_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:48.953409+00:00
-- url     : https://prove2.me/submissions/ca65af3a-8ab1-45cb-9481-3185b3260bf3

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_mem_filt_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] {ι : Type*}
namespace GlobalTheory.CompanionTheory.DSICKoszul
theorem _root_.solution (d : ι → Module.End ℂ Z) : Monotone (filt d) := by
  refine monotone_nat_of_le_succ fun m => ?_
  induction m with
  | zero => exact bot_le
  | succ m ih =>
    intro z hz
    rw [mem_filt_succ] at hz ⊢
    exact fun i => ih (hz i)
end GlobalTheory.CompanionTheory.DSICKoszul
