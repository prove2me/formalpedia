-- Prove2me | solution 1 for GlobalTheory.isUnit_of_isUnit_mk_of_le_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:38.980655+00:00
-- url     : https://prove2.me/submissions/46a7c7a3-9512-4ac9-b9be-353635328c93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S] {J : Ideal S}
    (hJ : J ≤ (⊥ : Ideal S).jacobson) {x : S} (hx : IsUnit (Ideal.Quotient.mk J x)) : IsUnit x :=
  have := isLocalHom_of_le_jacobson_bot J hJ
  IsUnit.of_map (Ideal.Quotient.mk J) x hx
end GlobalTheory
