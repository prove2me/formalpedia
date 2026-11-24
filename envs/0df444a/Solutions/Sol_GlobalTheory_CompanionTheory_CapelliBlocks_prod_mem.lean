-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliBlocks.prod_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:16.837744+00:00
-- url     : https://prove2.me/submissions/4fa145b8-23c2-4400-bb98-c86fe8e4796b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
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
namespace GlobalTheory.CompanionTheory.CapelliBlocks
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) :
    ∀ l : List (Module.End ℂ V), (∀ T ∈ l, ∀ v ∈ P, T v ∈ P) → (∃ T ∈ l, ∀ v, T v ∈ P) → ∀ v, l.prod v ∈ P
  | [], _, h, _ => by simp at h
  | T :: l, h1, h2, v => by
    rw [List.prod_cons, Module.End.mul_apply]
    obtain ⟨S, hS, hS'⟩ := h2
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hS' _
    · exact h1 T List.mem_cons_self _
        (solution P l (fun T hT => h1 T (List.mem_cons_of_mem _ hT)) ⟨S, hS, hS'⟩ v)
end GlobalTheory.CompanionTheory.CapelliBlocks
