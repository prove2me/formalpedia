-- Prove2me | solution 1 for GlobalTheory.T.isClosed_cartier_locus_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:18:33.30093+00:00
-- url     : https://prove2.me/submissions/58e88967-0894-4632-a98a-48a33d358add

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsClosedCartierLocusSupport
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsClosedCartierLocusSupportStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_isClosed_cartAt_e59396769268


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
theorem _root_.solution : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt <;> assumption)
end _root_.GlobalTheory.T
