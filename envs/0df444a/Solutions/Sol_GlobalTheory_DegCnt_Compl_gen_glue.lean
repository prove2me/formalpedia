-- Prove2me | solution 1 for GlobalTheory.DegCnt.Compl.gen_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:01:36.888343+00:00
-- url     : https://prove2.me/submissions/4fb8b217-b167-4086-b338-f5d115cae272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IdxSupRight
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Compl
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace GlobalTheory.DegCnt.Compl
theorem _root_.solution (M U U' : Submodule R W) (t : Finset W)
    (h : U ⊓ (M ⊔ U') = (M ⊓ U) ⊔ Submodule.span R (t : Set W)) :
    ∃ t' : Finset W, t'.card ≤ t.card ∧ U' ⊓ (M ⊔ U) = (M ⊓ U') ⊔ Submodule.span R (t' : Set W) := by
  have h1 : ∀ x : W, ∃ y : W, x ∈ t → y ∈ U' ∧ x - y ∈ M := by
    intro x
    by_cases hx : x ∈ t
    · have : x ∈ U ⊓ (M ⊔ U') := h ▸ Submodule.mem_sup_right (Submodule.subset_span hx)
      obtain ⟨m, hm, y, hy, e⟩ := Submodule.mem_sup.1 this.2
      exact ⟨y, fun _ => ⟨hy, by rw [← e]; simpa using hm⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using h1
  refine ⟨t.image f, Finset.card_image_le, ?_⟩
  have a : Submodule.span R (t.image f : Set W) ≤ U' := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact (hf x hx).1
  have b : M ⊔ Submodule.span R (t : Set W) = M ⊔ Submodule.span R (t.image f : Set W) := by
    apply le_antisymm
    · refine sup_le le_sup_left (Submodule.span_le.2 fun x hx => ?_)
      exact Submodule.mem_sup.2 ⟨_, (hf x hx).2, f x,
        Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)), by abel⟩
    · refine sup_le le_sup_left (Submodule.span_le.2 fun y hy => ?_)
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact Submodule.mem_sup.2 ⟨_, M.neg_mem (hf x hx).2, x, Submodule.subset_span hx, by abel⟩
  have c : (M ⊔ U) ⊓ (M ⊔ U') = M ⊔ Submodule.span R (t.image f : Set W) := by
    rw [sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), h, ← sup_assoc, sup_inf_self, b]
  have d : U' ⊓ (M ⊔ U) = ((M ⊔ U) ⊓ (M ⊔ U')) ⊓ U' := by
    rw [inf_assoc, inf_comm U', inf_eq_right.2 (le_sup_right : U' ≤ M ⊔ U')]
  rw [d, c, sup_comm M, sup_inf_assoc_of_le M a, sup_comm]
end GlobalTheory.DegCnt.Compl
