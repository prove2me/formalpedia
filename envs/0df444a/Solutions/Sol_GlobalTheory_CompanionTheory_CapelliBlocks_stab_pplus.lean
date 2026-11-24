-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliBlocks.stab_pplus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:21:39.133644+00:00
-- url     : https://prove2.me/submissions/b61cf691-2f8d-4ea8-bbfb-6a1e07d67bcf

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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {c d : Fin n}
    (hc : ε c = false) (hd : ε d = false) : ∀ v ∈ pplus ε E, E c d v ∈ pplus ε E := by
  rintro _ ⟨w, rfl⟩
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨⟨a, b⟩, ha, hb⟩ := i
  dsimp only at ha hb ⊢
  generalize w _ = x
  have h := LinearMap.congr_fun (hE c d a b) x
  have hda : d ≠ a := by rintro rfl; simp [ha] at hd
  rw [if_neg hda, zero_sub, LinearMap.sub_apply, sub_eq_iff_eq_add, LinearMap.neg_apply,
    Module.End.mul_apply, Module.End.mul_apply] at h
  rw [h]
  refine Submodule.add_mem _ (Submodule.neg_mem _ ?_) (mem_pplus ε E ha hb _)
  split_ifs
  · exact mem_pplus ε E ha hd _
  · simp
end GlobalTheory.CompanionTheory.CapelliBlocks
