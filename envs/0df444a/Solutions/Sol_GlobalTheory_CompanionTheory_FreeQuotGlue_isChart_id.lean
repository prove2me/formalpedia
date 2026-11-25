-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:41:26.834528+00:00
-- url     : https://prove2.me/submissions/e5eabfd1-a37e-4d6b-87b2-6b34ba14cf1b

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
theorem _root_.solution (X : Scheme.{0}) : IsChart (𝟙 X) (𝟙 X) ⊤ (⊤ : X.Opens).ι := by
  have : IsIso (⊤ : X.Opens).ι := X.topIso.isIso_hom
  refine ⟨rfl, inferInstance, inferInstance, inferInstance, inferInstance,
    𝟙 X ∣_ ⊤, morphismRestrict_ι _ _, ?_⟩
  exact IsPullback.of_horiz_isIso ⟨rfl⟩
end GlobalTheory.CompanionTheory.FreeQuotGlue
