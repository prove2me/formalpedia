-- Prove2me | solution 1 for GlobalTheory.T.conormal_finite_projective_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:59.816644+00:00
-- url     : https://prove2.me/submissions/1768b0c9-c6ee-466d-a250-e5098da112fe

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalFiniteProjectiveOfSmooth
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ConormalFiniteProjectiveOfSmoothStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__Conormal_finite_projective_cotangent_6ff6ba17bbab


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
theorem _root_.solution : ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth → ((Ideal.Quotient.mk I).comp φ).Smooth → Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | exact GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent <;> assumption)
end _root_.GlobalTheory.T
