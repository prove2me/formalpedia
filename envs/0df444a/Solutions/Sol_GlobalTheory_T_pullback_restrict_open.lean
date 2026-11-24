-- Prove2me | solution 1 for GlobalTheory.T.pullback_restrict_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:21:16.250236+00:00
-- url     : https://prove2.me/submissions/eb5d4616-71b4-4929-ad32-e37397c8033c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackRestrictOpen
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_PullbackRestrictOpenStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PullbackRestrict_isPullback_restrict_opens


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
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {P Q Y S : Scheme.{0}} {c : P ⟶ Q} {v : P ⟶ Y} {g : Q ⟶ S} {p : Y ⟶ S}, IsPullback c v g p → ∀ (W : S.Opens) (D : Y.Opens), D ≤ p ⁻¹ᵁ W → ∃ (h : D.toScheme ⟶ W.toScheme) (u : (v ⁻¹ᵁ D).toScheme ⟶ (g ⁻¹ᵁ W).toScheme), IsPullback u (v ∣_ D) (g ∣_ W) h := by
  first | exact @GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens | exact GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens | (intros; apply GlobalTheory.CompanionTheory.PullbackRestrict.isPullback_restrict_opens <;> assumption)
end _root_.GlobalTheory.T
