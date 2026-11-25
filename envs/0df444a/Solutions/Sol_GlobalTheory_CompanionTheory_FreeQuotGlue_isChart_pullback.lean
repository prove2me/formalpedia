-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:41:12.392628+00:00
-- url     : https://prove2.me/submissions/7bddb3a7-c92c-4b9b-ba3d-ff085fba5947

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
theorem _root_.solution {X Y : Scheme.{0}} (q : X ⟶ Y) [IsFinite q] [Flat q]
    [LocallyOfFinitePresentation q] [Surjective q] :
    IsChart (pullback.fst q q) (pullback.snd q q) ⊤ ((⊤ : X.Opens).ι ≫ q) := by
  have : IsIso (⊤ : X.Opens).ι := X.topIso.isIso_hom
  have hb : IsIso ((pullback.snd q q) ⁻¹ᵁ (⊤ : X.Opens)).ι := (pullback q q).topIso.isIso_hom
  let f := ((pullback.snd q q) ⁻¹ᵁ (⊤ : X.Opens)).ι
  refine ⟨rfl, inferInstance, inferInstance, inferInstance, inferInstance,
    f ≫ pullback.fst q q ≫ inv (⊤ : X.Opens).ι, by simp [f], ?_⟩
  refine IsPullback.of_iso (IsPullback.of_hasPullback q q) (asIso f).symm
    (asIso (⊤ : X.Opens).ι).symm (asIso (⊤ : X.Opens).ι).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [f]
  · rw [← cancel_mono (⊤ : X.Opens).ι]
    simp only [Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      morphismRestrict_ι]
    exact (IsIso.inv_hom_id_assoc f _).symm
  · simp
  · simp
end GlobalTheory.CompanionTheory.FreeQuotGlue
