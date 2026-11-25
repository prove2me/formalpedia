-- Prove2me | solution 1 for GlobalTheory.henselianLocalRing_localization_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:43.701909+00:00
-- url     : https://prove2.me/submissions/5cf8c4bd-3caf-43c3-b58a-f0b621541dc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_henselianLocalRing_of_finite
import Theorems.Thm_GlobalTheory_finite_localization_of_henselian

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
theorem _root_.solution (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [q.IsMaximal] : HenselianLocalRing (Localization.AtPrime q) :=
  have := finite_localization_of_henselian R q
  henselianLocalRing_of_finite R _
end GlobalTheory
