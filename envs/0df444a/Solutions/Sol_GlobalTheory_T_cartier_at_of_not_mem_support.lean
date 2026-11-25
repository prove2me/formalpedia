-- Prove2me | solution 1 for GlobalTheory.T.cartier_at_of_not_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:18.711769+00:00
-- url     : https://prove2.me/submissions/056e78df-9d41-458e-a432-4ee5b84ccf2a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfNotMemSupport
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartierAtOfNotMemSupportStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_notMem_support_9dc6313038df


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
theorem _root_.solution : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (x : X), x ∉ J.support → CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support <;> assumption)
end _root_.GlobalTheory.T
