-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GopEntries.wtA_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:15.819067+00:00
-- url     : https://prove2.me/submissions/1f38b939-45f2-427c-9d25-4073450f45d4

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreAnnApply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GopEntries
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.GopEntries
theorem _root_.solution (i : NC ε) (A : Finset (NC ε)) (hi : i ∈ A) :
    wtA A = wtA (A.erase i) + Pi.single i.1.1 1 - Pi.single i.1.2 1 := by
  funext c
  have key : ∀ (p : NC ε → Prop) [DecidablePred p],
      ((A.filter p).card : ℝ) = (((A.erase i).filter p).card : ℝ) + if p i then 1 else 0 := by
    intro p _
    conv_lhs => rw [← Finset.insert_erase hi, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]; simp
    · simp
  simp only [wtA, Pi.sub_apply, Pi.add_apply, Pi.single_apply]
  rw [key (fun i => i.1.1 = c), key (fun i => i.1.2 = c)]
  simp only [eq_comm (a := c)]
  ring
end GlobalTheory.CompanionTheory.GopEntries
