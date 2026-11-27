-- Prove2me | solution 1 for GlobalTheory.pic_mapAlgebra_mvPolynomial_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:02.451353+00:00
-- url     : https://prove2.me/submissions/cb752971-febc-4273-a76e-565ab17d7ebf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct AlgebraMonoidAlgebra
open AddMonoidAlgebra CommRing
open GlobalTheory
variable (A X : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
namespace GlobalTheory
theorem _root_.solution (σ : Type*) :
    Function.Bijective (Pic.mapAlgebra A (MvPolynomial σ A)) := by
  have : Subsingleton (Pic (AddMonoidAlgebra (FractionRing A) (σ →₀ ℕ))) :=
    inferInstanceAs (Subsingleton (Pic (MvPolynomial σ (FractionRing A))))
  exact pic_mapAlgebra_addMonoidAlgebra_bijective_of_subsingleton A (FractionRing A) (σ →₀ ℕ)
end GlobalTheory
