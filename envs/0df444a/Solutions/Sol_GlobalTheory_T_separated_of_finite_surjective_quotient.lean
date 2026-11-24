-- Prove2me | solution 1 for GlobalTheory.T.separated_of_finite_surjective_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:28.679126+00:00
-- url     : https://prove2.me/submissions/8a794922-bf04-4627-a9c2-adcafd0459b1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_SeparatedOfFiniteSurjectiveQuotient
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_SeparatedOfFiniteSurjectiveQuotientStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotientSide_isSeparated_target_of_finite_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q → IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left → IsSeparated Y.hom := by
  first | exact @GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | exact GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | (intros; apply GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective <;> assumption)
end _root_.GlobalTheory.T
