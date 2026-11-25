-- Prove2me | solution 1 for GlobalTheory.T.exists_smooth_affine_presentation_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:02:20.59633+00:00
-- url     : https://prove2.me/submissions/1c0d665a-36ad-4936-92ac-e0fef54aac5f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsSmoothAffinePresentationPair
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsSmoothAffinePresentationPairStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__Charts_smooth_affine_chart_3ba3a084d834


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (U : X.affineOpens), Smooth g → Smooth (Z.subschemeι ≫ g) → ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | exact GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart <;> assumption)
end _root_.GlobalTheory.T
