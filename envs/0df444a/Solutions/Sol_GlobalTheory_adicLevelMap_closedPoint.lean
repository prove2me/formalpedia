-- Prove2me | solution 1 for GlobalTheory.adicLevelMap_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:22.249033+00:00
-- url     : https://prove2.me/submissions/0adf43fb-5cfb-4bbe-944c-3a709edf7e9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]
namespace GlobalTheory
theorem _root_.solution (hI : I ≠ ⊤) {m n : ℕ} (h : m + 1 ≤ n + 1) :
    haveI := isLocalRing_quotient_pow hI m
    haveI := isLocalRing_quotient_pow hI n
    adicLevelMap I h (closedPoint (R ⧸ I ^ (m + 1))) = closedPoint (R ⧸ I ^ (n + 1)) := by
  have := isLocalRing_quotient_pow hI m
  have := isLocalRing_quotient_pow hI n
  have : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.factorPow I h)).hom :=
    IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right h))
  exact Spec_closedPoint
end GlobalTheory
