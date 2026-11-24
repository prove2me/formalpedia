-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSNormLt.abs_tt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:57:51.265239+00:00
-- url     : https://prove2.me/submissions/86d195c4-eb11-4803-a5f5-0d16e2753cf4

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IndOfNot
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_ind_of_not
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_tt_anti
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_tt_of
import Theorems.Thm_GlobalTheory_CompanionTheory_DSNormLt_abs_sig
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
theorem _root_.solution {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : |tt A a b| ≤ 1 := by
  have key : ∀ a b : Fin n, (ε a = true ∧ ε b = false) → |tt A a b| ≤ 1 := fun a b h => by
    rw [tt_of A h]
    split_ifs
    · exact abs_sig a b
    · rw [abs_neg]; exact abs_sig a b
  by_cases h : ε a = true ∧ ε b = false
  · exact key a b h
  by_cases h' : ε b = true ∧ ε a = false
  · rw [tt_anti, abs_neg]; exact key b a h'
  unfold tt
  rw [ind_of_not _ h', ind_of_not _ h', ind_of_not _ h, ind_of_not _ h]
  simpa using abs_sig a b
end GlobalTheory.CompanionTheory.DSNormLt
