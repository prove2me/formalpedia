-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.hasAffineChart_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:53.69493+00:00
-- url     : https://prove2.me/submissions/0e390a35-0c8a-48d0-823a-81e32f0c7a77

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
theorem _root_.solution {P X : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) :
    HasAffineChart a b V ↔ ∃ (Y : Scheme.{0}) (q : V.toScheme ⟶ Y), IsAffine Y ∧ IsChart a b V q := by
  constructor
  · rintro ⟨h, Y, q, a', hY, h1, h2, h3, h4, h5, h6⟩
    exact ⟨Y, q, hY, h, h1, h2, h3, h4, a', h5, h6⟩
  · rintro ⟨Y, q, hY, h, h1, h2, h3, h4, a', h5, h6⟩
    exact ⟨h, Y, q, a', hY, h1, h2, h3, h4, h5, h6⟩
end GlobalTheory.CompanionTheory.FreeQuotGlue
