-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CommNil.exists_rel_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:18.658149+00:00
-- url     : https://prove2.me/submissions/99b41820-2935-4759-b7aa-bf13599fb996

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CommNil
open Module
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.CommNil
theorem _root_.solution [FiniteDimensional ℂ V] (W' W : Submodule ℂ V) (h : W' ≤ W) :
    ∃ Y : Submodule ℂ V, Y ⊔ W' = W ∧ finrank ℂ Y + finrank ℂ W' = finrank ℂ W := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W'
  have hsup : C ⊓ W ⊔ W' = W := by
    rw [sup_comm, ← sup_inf_assoc_of_le C h, hC.sup_eq_top, top_inf_eq]
  have hinf : C ⊓ W ⊓ W' = ⊥ := by
    have hle : C ⊓ W ⊓ W' ≤ C ⊓ W' := inf_le_inf_right W' inf_le_left
    rw [inf_comm C W', hC.inf_eq_bot] at hle
    exact le_bot_iff.1 hle
  refine ⟨C ⊓ W, hsup, ?_⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (C ⊓ W) W'
  rw [hsup, hinf, finrank_bot, add_zero] at hdim
  exact hdim.symm
end GlobalTheory.CompanionTheory.CommNil
