-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:59.31162+00:00
-- url     : https://prove2.me/submissions/08770bc2-af5b-4ca7-92d2-604c1c740a1e

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ChartRestrictPreimageOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_InvariantOpenChartPreimageStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_GlueQuotientChartsCoverStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedChartsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_QuotientOfAffineChartCover
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_exists_isOpenImmersion
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_exists_common
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_prop_of_charts
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_apply_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_effectiveEpi
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_flat
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_isFinite
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_lfp
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_stable
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_IsChart_surjective
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotGlue_hasAffineChart_iff
import Theorems.Thm_GlobalTheory_T_glue_quotient_charts_cover
import Theorems.Thm_GlobalTheory_T_pullback_of_glued_charts
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_surjective_29b40d414390


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
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
theorem _root_.solution : ∀ {P X : Scheme.{0}} (a b : P ⟶ X), (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ HasAffineChart a b V) → ∃ (Y : Scheme.{0}) (q : X ⟶ Y), IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧ IsPullback a b q q := by
  intro P X a b h
  let 𝒰 : Set X.Opens := {V | HasAffineChart a b V}
  have hU (U : 𝒰) := (hasAffineChart_iff a b U.1).1 U.2
  choose Y q hY hq using hU
  let R : X → X → Prop := fun x y ↦ ∃ p : P, a p = x ∧ b p = y
  have hk (U V : 𝒰) (h : U.1 ≤ V.1) := (hq V).exists_isOpenImmersion (hq U) h
  choose k hk hqk using hk
  obtain ⟨Y', π, em, hem, hcomm, hpre, hsurj⟩ := GlobalTheory.T.glue_quotient_charts_cover R 𝒰
    (fun U hU V hV x hx hx' ↦ by
      obtain ⟨W, h1, h2, h3, h4⟩ := exists_common hU hV x hx hx'
      exact ⟨W, h1, h2, h3, h4⟩)
    (fun x ↦ by
      obtain ⟨V, h1, h2⟩ := h x
      exact ⟨⟨V, h2⟩, h1⟩)
    Y q (fun U ↦ by have := (hq U).effectiveEpi; infer_instance)
    (fun U ↦ by have := (hq U).surjective; exact Surjective.surj)
    (fun U u v ↦ (hq U).apply_eq_iff u v)
    (fun U x y ⟨p, h1, h2⟩ hx ↦ by
      have : p ∈ a ⁻¹ᵁ U.1 := by change a p ∈ U.1; rwa [h1]
      rw [(hq U).stable] at this
      rw [← h2]; exact this)
    k hk hqk
  refine ⟨Y', π, ?_, ?_, ?_, ?_, ?_⟩
  · exact prop_of_charts (@IsFinite.{0}) π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).isFinite
  · exact prop_of_charts @Flat.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).flat
  · exact prop_of_charts @LocallyOfFinitePresentation.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).lfp
  · exact prop_of_charts @Surjective.{0} π _ Y q em hcomm hpre hsurj fun U ↦ (hq U).surjective
  · exact GlobalTheory.T.pullback_of_glued_charts a b π _ Y q em hq hcomm hpre hsurj
end GlobalTheory.CompanionTheory.FreeQuotGlue
