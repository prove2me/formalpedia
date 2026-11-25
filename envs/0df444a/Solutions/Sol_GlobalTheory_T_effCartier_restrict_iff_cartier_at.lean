-- Prove2me | solution 1 for GlobalTheory.T.effCartier_restrict_iff_cartier_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:18:47.966562+00:00
-- url     : https://prove2.me/submissions/faf6c5a3-1f6d-4221-aac6-0cdcc1b984ce

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierRestrictIffCartierAt
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierRestrictIffCartierAtStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_effCartier_comap_opens_iff_53f9aad034ca


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
theorem _root_.solution : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (O : X.Opens), FinalTheorems.EffCartier (J.comap O.ι) ↔ ∀ x ∈ O, CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff <;> assumption)
end _root_.GlobalTheory.T
