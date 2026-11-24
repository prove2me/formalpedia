-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SpreadingModels.properSpreads
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:06:24.373904+00:00
-- url     : https://prove2.me/submissions/42f922d1-678d-4076-a1f9-36f5f7eaf262

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsProperSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ae_unique_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_fp_sections
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_finiteType_lvl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_exists_limit_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SpreadingModels
open GlobalTheory.CompanionTheory.Ultra
namespace GlobalTheory.CompanionTheory.SpreadingModels
theorem _root_.solution : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) := by
  intro R R₀ _ _ φ Y Y₀ f f₀ π ⟨hft, hlfp, hqc, hqs, hpb⟩ hprop
  have hprop' : IsProper f := hprop
  have hval : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hprop'
    exact hprop'.1.1.1
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  haveI : QuasiSeparatedSpace Y₀ := quasiSeparatedSpace_of_quasiSeparated f₀
  have hfp := fp_sections f₀ (R₀ := R₀)
  obtain ⟨S₀, hS₀⟩ := hft.out
  have hS₀f : (S₀ : Set R₀).Finite := S₀.finite_toSet
  suffices h : ∃ F, IsProper (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (lvlHom φ hS₀ F)))) by
    obtain ⟨F, hF⟩ := h
    exact ⟨lvl φ S₀ F, inferInstance, lvlHom φ hS₀ F, (lvl φ S₀ F).val.toRingHom, rfl,
      finiteType_lvl φ hS₀f F, hF⟩
  by_contra hcon
  push_neg at hcon
  have hS : ∀ F, ∃ S : ValuativeCommSq (pullback.snd f₀ (Spec.map (CommRingCat.ofHom
      (lvlHom φ hS₀ F)))), ¬ Nonempty (Unique S.commSq.LiftStruct) := by
    intro F
    by_contra h
    push_neg at h
    apply hcon F
    rw [IsProper.eq_valuativeCriterion]
    exact ⟨⟨⟨h, inferInstance⟩, inferInstance⟩, inferInstance⟩
  choose S hS using hS
  let U : Ultrafilter (Finset R) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset R)) ≤ atTop := Ultrafilter.of_le _
  let β : ∀ F, lvl φ S₀ F →+* (S F).R := fun F => (Spec.preimage (S F).i₂).hom
  have hβ : ∀ F, (S F).i₂ = Spec.map (CommRingCat.ofHom (β F)) := fun F => by simp [β]
  obtain ⟨ρ, hρ⟩ := exists_limit_hom φ hS₀ (V := fun F => (S F).R) β U hU
  obtain ⟨F, hF⟩ := (ae_unique_lift f₀ hfp hpb hval U (lvlHom φ hS₀) S β hβ ρ hρ).exists
  exact hS F hF
end GlobalTheory.CompanionTheory.SpreadingModels
