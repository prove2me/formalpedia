-- Prove2me | solution 1 for GlobalTheory.isUnit_of_isUnit_map_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:18:08.026062+00:00
-- url     : https://prove2.me/submissions/f0e83f1d-4ee5-486e-a4a6-6c71648e4ea7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Theorems.Thm_GlobalTheory_isUnit_of_isUnit_map_of_ker_le_jacobson

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
theorem _root_.solution (I : Ideal B) [HenselianRing B I] (π : B →+* C)
    (hπ : Function.Surjective π) (hI : ∀ b, b ∈ I ↔ π b = 0) {b : B} (hb : IsUnit (π b)) :
    IsUnit b :=
  isUnit_of_isUnit_map_of_ker_le_jacobson π hπ
    (fun x hx => HenselianRing.jac (I := I) ((hI x).mpr hx)) hb
end GlobalTheory
