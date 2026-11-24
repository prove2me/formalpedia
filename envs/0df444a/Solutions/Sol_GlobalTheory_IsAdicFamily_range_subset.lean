-- Prove2me | solution 1 for GlobalTheory.IsAdicFamily.range_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:52.978013+00:00
-- url     : https://prove2.me/submissions/b05d686e-4f74-408e-814d-2e4f1c58a8c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_range_subset_of_closedPoint_mem
import Theorems.Thm_GlobalTheory_IsAdicFamily_closedPoint_eq

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
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f) {U : X.Opens}
    (hU : haveI := isLocalRing_quotient_pow hI 0; f 0 (closedPoint (R ⧸ I ^ (0 + 1))) ∈ U)
    (n : ℕ) : Set.range (f n) ⊆ U :=
  haveI := isLocalRing_quotient_pow hI n
  range_subset_of_closedPoint_mem (f n) (by rwa [hf.closedPoint_eq hI n])
end IsAdicFamily
end GlobalTheory
