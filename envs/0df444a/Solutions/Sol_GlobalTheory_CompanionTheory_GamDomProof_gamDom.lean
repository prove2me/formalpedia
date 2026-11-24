-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GamDomProof.gamDom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:10:41.128822+00:00
-- url     : https://prove2.me/submissions/1c6973ba-0e8a-4e83-b669-4d89be9b22d7

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CardOther
import Theorems.Thm_GlobalTheory_CompanionTheory_GamDomProof_gam_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_GamDomProof_pos_le
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
open CompanionTheory.D.DSIC
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GamDomProof
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.GamDomProof
theorem _root_.solution : CompanionTheory.D.DSIC.GamDom := by
  intro n ε lam ⟨hanti, hint⟩
  choose m hm using hint
  have hm' : StrictAnti m := by
    intro a b hab
    have := hanti hab
    have h : (m b : ℝ) < m a := by rw [← hm, ← hm]; linarith
    exact_mod_cast h
  refine ⟨fun a => m a + (univ.filter fun b => b < a ∧ ε b = ε a).card
    + (if ε a = true then (nb ε false : ℤ) else 0), fun a => ?_, fun c d hcd e => ?_⟩
  · rw [gam_eq, hm]
    push_cast
    rfl
  · have := pos_le ε m hm' c d hcd e
    have h2 : (if ε d = true then (nb ε false : ℤ) else 0) = (if ε c = true then (nb ε false : ℤ) else 0) := by
      rw [e]
    simp only [h2]
    linarith
end GlobalTheory.CompanionTheory.GamDomProof
