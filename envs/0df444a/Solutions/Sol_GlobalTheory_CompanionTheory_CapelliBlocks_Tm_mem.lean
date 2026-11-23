-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliBlocks.Tm_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:36.863801+00:00
-- url     : https://prove2.me/submissions/9b48217b-afa4-4319-9c91-ed21d090b906

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkBijective
import Theorems.Thm_GlobalTheory_CompanionTheory_CapelliBlocks_mem_pplus
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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n}
    (ha : ε a = true) (hb : ε b = false) (u : ℂ) (v : V) : Tm E u a b v ∈ pplus ε E := by
  have hab : a ≠ b := by rintro rfl; simp [ha] at hb
  rw [Tm, if_neg hab, zero_add]
  exact mem_pplus ε E ha hb v
end GlobalTheory.CompanionTheory.CapelliBlocks
