-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GopEntries.gFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:26:45.173802+00:00
-- url     : https://prove2.me/submissions/0ccd6c40-704d-4793-8229-d541fddd758e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreAnnApply
import Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_hh_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_coef_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_Gop_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_wtA_erase
import Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_exists_of_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_gg_diag
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
theorem _root_.solution : GFacts := by
  intro n ε
  refine ⟨gg, fun V _ _ c d x A => Gop_apply c d x A, fun c d A B => ?_, fun c d A B h => ?_,
    gg_diag, fun c d A hdc => ?_⟩
  · unfold gg
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [coef_symm, hh_symm]
  · obtain ⟨i, j, hc, hi, hj, e⟩ := exists_of_ne h
    refine ⟨?_, ?_⟩
    · rw [← Finset.card_erase_add_one hi, e, Finset.card_erase_add_one hj]
    · rw [wtA_erase i A hi, wtA_erase j B hj, e]
      rcases hc with ⟨a, b, f⟩ | ⟨a, b, f⟩
      · rw [a, b, f]; abel
      · rw [a, b, f]; abel
  · by_contra h
    obtain ⟨i, j, hc, hi, hj, e⟩ := exists_of_ne h
    have hn : i ∉ (A1 ε).erase j := e ▸ Finset.notMem_erase i A
    apply hn
    simp only [A1, mem_filter, mem_univ, true_and, mem_erase] at hj ⊢
    rcases hc with ⟨a, b, f⟩ | ⟨a, b, f⟩
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hdc.ne (b.symm.trans a)
      · rw [a, f]; rw [b] at hj; exact hj.trans hdc
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hdc.ne (a.symm.trans b)
      · rw [a, f]; rw [b] at hj; exact hdc.trans hj
end GlobalTheory.CompanionTheory.GopEntries
