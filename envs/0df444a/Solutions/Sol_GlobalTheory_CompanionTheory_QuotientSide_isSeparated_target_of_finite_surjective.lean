-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:28.711562+00:00
-- url     : https://prove2.me/submissions/d283fcb1-8c27-4286-a6cb-54f8a8a38cca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_SeparatedOfFiniteSurjectiveQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotientSide_isSeparated_of_finite_surjective

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotientSide
namespace GlobalTheory.CompanionTheory.QuotientSide
theorem _root_.solution :
    ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q →
      IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left →
      IsSeparated Y.hom := by
  intro S X Y K q p₁ p₂ _ _ hX hq hs
  exact isSeparated_of_finite_surjective X.hom Y.hom q.left (Over.w q)
end GlobalTheory.CompanionTheory.QuotientSide
