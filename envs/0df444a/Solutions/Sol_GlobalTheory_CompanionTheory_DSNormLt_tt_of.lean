-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.tt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:20.149798+00:00
-- url     : https://prove2.me/submissions/77954523-e9a5-4be9-81f0-c7d3734baedf

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_ind_of_not
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_ind_of
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSNormLt
open CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSNormLt
theorem _root_.solution {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ε a = true ∧ ε b = false) :
    tt A a b = if ((⟨(a, b), h⟩ : NC ε) ∈ A ↔ (⟨(a, b), h⟩ : NC ε) ∈ A1 ε) then sig a b else - sig a b := by
  have h' : ¬ (ε b = true ∧ ε a = false) := by simp [h.1]
  have hab : a ≠ b := by rintro rfl; simp [h.1] at h
  unfold tt
  rw [ind_of_not _ h', ind_of_not _ h', ind_of _ h, ind_of _ h]
  have hm : (⟨(a, b), h⟩ : NC ε) ∈ A1 ε ↔ b < a := by simp [A1]
  simp only [hm]
  unfold sig
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> by_cases h2 : (⟨(a, b), h⟩ : NC ε) ∈ A <;>
    simp [h1, h1.not_gt, h2] <;> norm_num
end GlobalTheory.CompanionTheory.DSNormLt
