-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:10:40.237476+00:00
-- url     : https://prove2.me/submissions/9e7b2197-104d-4ec9-9217-e8f47749bcc0

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedCharts
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_isIso_restrict_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
theorem _root_.solution {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type}
    (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y')
    [∀ j, IsOpenImmersion (em j)] (hch : ∀ j, IsChart a b (V j) (q j))
    (hc : ∀ j, (V j).ι ≫ π = q j ≫ em j) (hpre : ∀ j, π ⁻¹ᵁ (em j).opensRange = V j)
    (hcov : ∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) : IsPullback a b π π := by

  have hV : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨j, z, hz⟩ := hcov (π x)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨j, ?_⟩
    rw [← hpre j, Scheme.Hom.mem_preimage]
    exact ⟨z, hz⟩

  have hw : a ≫ π = b ≫ π := by
    refine Scheme.Cover.hom_ext
      (P.openCoverOfIsOpenCover (fun j => b ⁻¹ᵁ V j)
        (by unfold TopologicalSpace.IsOpenCover; exact b.iSup_preimage_eq_top hV)) _ _ fun j => ?_
    obtain ⟨-, -, -, -, -, a', ha', hsq⟩ := hch j
    change (b ⁻¹ᵁ V j).ι ≫ a ≫ π = (b ⁻¹ᵁ V j).ι ≫ b ≫ π
    calc (b ⁻¹ᵁ V j).ι ≫ a ≫ π = a' ≫ (V j).ι ≫ π := by
          rw [← Category.assoc, ← ha', Category.assoc]
      _ = a' ≫ q j ≫ em j := by rw [hc j]
      _ = (b ∣_ V j) ≫ q j ≫ em j := by rw [← Category.assoc, hsq.w, Category.assoc]
      _ = (b ∣_ V j) ≫ (V j).ι ≫ π := by rw [hc j]
      _ = (b ⁻¹ᵁ V j).ι ≫ b ≫ π := by rw [morphismRestrict_ι_assoc]

  have hiso : IsIso (pullback.lift a b hw) := by
    rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
        (fun j => pullback.snd π π ⁻¹ᵁ V j) ((pullback.snd π π).iSup_preimage_eq_top hV)]
    intro j
    rw [MorphismProperty.isomorphisms.iff]
    exact IsChart.isIso_restrict_lift (hch j) (hc j) (hpre j) hw
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift a b hw))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
end GlobalTheory.CompanionTheory.FreeQuotGlue
