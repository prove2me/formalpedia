-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZetaHighest.gam_false
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:15:51.548277+00:00
-- url     : https://prove2.me/submissions/b6ffdcd5-c22b-4fd9-8335-ae662d2e6d01

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkStrictMono
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_blk_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_card_below
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_card_total
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_wt_false
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
theorem _root_.solution (ε : Fin n → Bool) (lam : Fin n → ℝ) (i : Fin (nb ε false)) :
    gam ε lam (blk ε false i) = lam (blk ε false i) - ((n : ℝ) - 1) / 2 + (i : ℕ) := by
  have h1 := card_total ε (blk ε false i)
  have h2 := wt_false ε _ (blk_mem ε false i)
  have h3 := card_below ε false i
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]
  rw [h2]
  rw [h3] at h1 ⊢
  linarith
end GlobalTheory.CompanionTheory.ZetaHighest
