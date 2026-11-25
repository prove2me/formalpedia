-- Prove2me | solution 1 for GlobalTheory.T.locally_principal_of_conormal_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:28.565753+00:00
-- url     : https://prove2.me/submissions/07c3e989-011a-4951-ab48-12566fb00a8c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfConormalRankOne
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfConormalRankOneStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_rankAtStalk_eq_one_ac4f75c6d205


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
theorem _root_.solution : ∀ {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), Module.rankAtStalk I.Cotangent P = 1 → LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one <;> assumption)
end _root_.GlobalTheory.T
