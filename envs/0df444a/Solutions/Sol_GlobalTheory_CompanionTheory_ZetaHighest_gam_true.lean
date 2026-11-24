-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZetaHighest.gam_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:57.529424+00:00
-- url     : https://prove2.me/submissions/4709ffdb-1d23-4a61-b47e-fd0530a124bb

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkStrictMono
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_blk_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_card_below
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_card_total
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_card_other
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_wt_true
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZetaHighest
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ZetaHighest
theorem _root_.solution (ε : Fin n → Bool) (lam : Fin n → ℝ) (i : Fin (nb ε true)) :
    gam ε lam (blk ε true i) = lam (blk ε true i) - ((n : ℝ) - 1) / 2 + (nb ε false : ℝ) + (i : ℕ) := by
  have h1 := card_total ε (blk ε true i)
  have h2 := wt_true ε _ (blk_mem ε true i)
  have h3 := card_below ε true i
  have h4 := card_other ε _ (blk_mem ε true i)
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]
  rw [h2]
  rw [h3] at h1 ⊢
  linarith
end GlobalTheory.CompanionTheory.ZetaHighest
