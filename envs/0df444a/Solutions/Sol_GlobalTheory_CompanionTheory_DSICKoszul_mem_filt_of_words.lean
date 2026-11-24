-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.mem_filt_of_words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:25:46.522606+00:00
-- url     : https://prove2.me/submissions/17649e96-35ab-4176-b0ec-022233fa4906

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_mem_filt_succ
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] {ι : Type*}
namespace GlobalTheory.CompanionTheory.DSICKoszul
theorem _root_.solution (d : ι → Module.End ℂ Z) (m : ℕ) (z : Z)
    (h : ∀ l : List ι, l.length = m → (l.map d).prod z = 0) : z ∈ filt d m := by
  induction m generalizing z with
  | zero => simpa [filt] using h [] rfl
  | succ m ih =>
    rw [mem_filt_succ]
    intro i
    refine ih _ fun l hl => ?_
    have := h (l ++ [i]) (by simp [hl])
    simpa using this
end GlobalTheory.CompanionTheory.DSICKoszul
