-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_preimage_opensRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:15.934127+00:00
-- url     : https://prove2.me/submissions/8ec5fea8-2127-4960-8fa2-ab29c678177f

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackOfGluedCharts

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
theorem _root_.solution {X Y Y' : Scheme.{0}} (π : X ⟶ Y') (V : X.Opens)
    (q : V.toScheme ⟶ Y) (em : Y ⟶ Y') [IsOpenImmersion em] (hc : V.ι ≫ π = q ≫ em)
    (hpre : π ⁻¹ᵁ em.opensRange = V) : IsPullback q V.ι em π :=
  IsOpenImmersion.isPullback q V.ι em π hc (by rw [hpre, Scheme.Opens.opensRange_ι])
end GlobalTheory.CompanionTheory.FreeQuotGlue
