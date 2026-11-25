-- Prove2me | solution 1 for GlobalTheory.T.cartier_at_of_locally_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:56.730929+00:00
-- url     : https://prove2.me/submissions/bf9cc7d6-7213-4fc0-bf75-dd957e2f1dbf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipal
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfLocallyPrincipalStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_locPrincipal_47d661a47a8e


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
theorem _root_.solution : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData) (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal <;> assumption)
end _root_.GlobalTheory.T
