-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliBlocks.blk_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:40.286479+00:00
-- url     : https://prove2.me/submissions/27c69b1d-aa1d-4cab-878d-a3e5f61b3187

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_blk_val
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
open Finset Equiv
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliBlocks
open Formalism.REAL CompanionTheory.D.DSIC
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CapelliBlocks
theorem _root_.solution (ε : Fin n → Bool) : Function.Bijective (Sum.elim (blk ε false) (blk ε true)) := by
  have hinj : ∀ s, Function.Injective (blk ε s) := fun s =>
    ((univ.filter fun a => ε a = s).orderEmbOfFin rfl).injective
  have hsur : ∀ a, ∃ k, blk ε (ε a) k = a := fun a => by
    have : a ∈ Set.range ((univ.filter fun b => ε b = ε a).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      simp
    exact this
  constructor
  · refine Function.Injective.sumElim (hinj false) (hinj true) fun a b h => ?_
    have h1 := blk_val ε false a
    rw [h, blk_val ε true b] at h1
    exact absurd h1 (by simp)
  · intro a
    have h := hsur a
    cases ha : ε a
    · rw [ha] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨Sum.inl k, hk⟩
    · rw [ha] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨Sum.inr k, hk⟩
end GlobalTheory.CompanionTheory.CapelliBlocks
