-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GamDomProof.pos_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:14.732797+00:00
-- url     : https://prove2.me/submissions/e81502aa-6a17-40b4-a43e-c36fd71527c5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CardOther
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
theorem _root_.solution (ε : Fin n → Bool) (m : Fin n → ℤ) (hm : StrictAnti m) (c d : Fin n) (hcd : c < d)
    (e : ε c = ε d) :
    m d + (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      m c + (univ.filter fun b => b < c ∧ ε b = ε c).card := by
  have h1 : (univ.filter fun b => b < d ∧ ε b = ε d).card ≤
      (univ.filter fun b => b < c ∧ ε b = ε c).card + (Ico c d).card := by
    refine le_trans (card_le_card ?_) (card_union_le _ _)
    intro b hb
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_Ico] at hb ⊢
    rcases lt_or_ge b c with h | h
    · exact Or.inl ⟨h, hb.2.trans e.symm⟩
    · exact Or.inr ⟨h, hb.1⟩
  have h2 : (Ico c d).card ≤ (Ioc (m d) (m c)).card := by
    refine card_le_card_of_injOn m ?_ hm.injective.injOn
    intro b hb
    simp only [coe_Ico, coe_Ioc, Set.mem_Ico, Set.mem_Ioc] at hb ⊢
    exact ⟨hm hb.2, hm.antitone hb.1⟩
  rw [Int.card_Ioc] at h2
  have h3 := hm hcd
  omega
end GlobalTheory.CompanionTheory.GamDomProof
