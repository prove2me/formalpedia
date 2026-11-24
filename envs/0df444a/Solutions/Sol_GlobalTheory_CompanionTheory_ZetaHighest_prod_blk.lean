-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZetaHighest.prod_blk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:01.033899+00:00
-- url     : https://prove2.me/submissions/300aec1b-f136-4803-b5a2-0bcca637e412

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkStrictMono
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_blk_strictMono
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_blk_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_blk_surj
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZetaHighest
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ZetaHighest
theorem _root_.solution (ε : Fin n → Bool) (s : Bool) (f : Fin n → ℂ) :
    ∏ i, f (blk ε s i) = ∏ a ∈ univ.filter (fun a => ε a = s), f a := by
  refine Finset.prod_bij (fun i _ => blk ε s i) ?_ ?_ ?_ ?_
  · intro i _; simp [blk_mem]
  · intro i _ j _ h; exact (blk_strictMono ε s).injective h
  · intro a ha
    obtain ⟨i, hi⟩ := blk_surj ε s a (Finset.mem_filter.1 ha).2
    exact ⟨i, mem_univ _, hi⟩
  · intro i _; rfl
end GlobalTheory.CompanionTheory.ZetaHighest
