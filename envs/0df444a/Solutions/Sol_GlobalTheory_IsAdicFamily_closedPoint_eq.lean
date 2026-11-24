-- Prove2me | solution 1 for GlobalTheory.IsAdicFamily.closedPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:39:51.625371+00:00
-- url     : https://prove2.me/submissions/89605554-26b2-43e6-be4b-ed376a78fe56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_IsAdicFamily_of_le
import Theorems.Thm_GlobalTheory_adicLevelMap_closedPoint

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
namespace IsAdicFamily
theorem _root_.solution (hI : I ≠ ⊤) {X : Scheme.{u}}
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f) (n : ℕ) :
    haveI := isLocalRing_quotient_pow hI n
    haveI := isLocalRing_quotient_pow hI 0
    f n (closedPoint (R ⧸ I ^ (n + 1))) = f 0 (closedPoint (R ⧸ I ^ (0 + 1))) := by
  rw [← hf.of_le (Nat.zero_le n)]
  refine Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _).symm
  exact congrArg (f n) (adicLevelMap_closedPoint hI _).symm
end IsAdicFamily
end GlobalTheory
