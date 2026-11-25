-- Prove2me | solution 1 for GlobalTheory.T.locally_principal_of_cartier_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:27.049862+00:00
-- url     : https://prove2.me/submissions/a016616f-40a7-4920-864f-3be01e0d125b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAt
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAtStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_cartAt_2a84a79b84c2


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
theorem _root_.solution : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData) (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), CartAt Z (U.2.fromSpec q) → LocPrincipal (Z.ideal U) q.asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt <;> assumption)
end _root_.GlobalTheory.T
