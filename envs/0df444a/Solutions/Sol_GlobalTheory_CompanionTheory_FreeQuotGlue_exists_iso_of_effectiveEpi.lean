-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.exists_iso_of_effectiveEpi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:13.694751+00:00
-- url     : https://prove2.me/submissions/26d6e997-3faf-4895-8058-7742b81a7aa6

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_InvariantOpenChartPreimageStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_GlueQuotientChartsCoverStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedChartsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_QuotientOfAffineChartCover

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
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
theorem _root_.solution {T Y₁ Y₂ : Scheme.{0}} (q₁ : T ⟶ Y₁) (q₂ : T ⟶ Y₂)
    [EffectiveEpi q₁] [EffectiveEpi q₂]
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ T), g₁ ≫ q₁ = g₂ ≫ q₁ ↔ g₁ ≫ q₂ = g₂ ≫ q₂) :
    ∃ e : Y₁ ≅ Y₂, q₁ ≫ e.hom = q₂ := by
  let f : Y₁ ⟶ Y₂ := EffectiveEpi.desc q₁ q₂ fun {Z} g₁ g₂ e ↦ (h Z g₁ g₂).1 e
  let g : Y₂ ⟶ Y₁ := EffectiveEpi.desc q₂ q₁ fun {Z} g₁ g₂ e ↦ (h Z g₁ g₂).2 e
  have hf : q₁ ≫ f = q₂ := EffectiveEpi.fac _ _ _
  have hg : q₂ ≫ g = q₁ := EffectiveEpi.fac _ _ _
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · rw [← cancel_epi q₁, reassoc_of% hf, hg, Category.comp_id]
  · rw [← cancel_epi q₂, reassoc_of% hg, hf, Category.comp_id]
end GlobalTheory.CompanionTheory.FreeQuotGlue
