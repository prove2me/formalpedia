-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GamDomProof.card_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:10.53484+00:00
-- url     : https://prove2.me/submissions/69558c0b-41c3-4f60-8f54-959511a2e4ce

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
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) :
    ((A1 ε).filter fun i => i.1.1 = a).card =
      if ε a = true then (univ.filter fun b => b < a ∧ ε b ≠ ε a).card else 0 := by
  split_ifs with h
  · refine card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi hx hy ⊢
      obtain ⟨h1, rfl⟩ := hi
      exact ⟨h1, by simp [hx, hy]⟩
    · rintro ⟨⟨x, y⟩, hx, hy⟩ hi ⟨⟨x', y'⟩, hx', hy'⟩ hi' e
      simp only [A1, mem_filter, mem_univ, true_and] at hi hi' e
      apply Subtype.ext
      simp [hi.2, hi'.2, e]
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨(a, b), h, by simpa [h] using hb.2⟩, ?_, rfl⟩
      simp [A1, hb.1]
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨x, y⟩, hx, hy⟩ _ e
    simp only at e hx
    exact h (e ▸ hx)
end GlobalTheory.CompanionTheory.GamDomProof
