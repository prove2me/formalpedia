-- Prove2me | solution 1 for GlobalTheory.isLocalRing_of_surjective_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:41.469048+00:00
-- url     : https://prove2.me/submissions/b7de7780-8768-4c5e-be12-fac79701ce0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Theorems.Thm_GlobalTheory_isUnit_of_isUnit_map_of_henselian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
namespace GlobalTheory
theorem _root_.solution [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
    (π : B →+* C) (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0) : IsLocalRing C := by
  have : Nontrivial C := by
    by_contra hC
    rw [not_nontrivial_iff_subsingleton] at hC
    exact not_isUnit_zero (isUnit_of_isUnit_map_of_henselian I π hπ hI (b := 0)
      (isUnit_of_subsingleton _))
  exact IsLocalRing.of_surjective' π hπ
end GlobalTheory
