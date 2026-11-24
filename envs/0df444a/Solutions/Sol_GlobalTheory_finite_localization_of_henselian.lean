-- Prove2me | solution 1 for GlobalTheory.finite_localization_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:42.035156+00:00
-- url     : https://prove2.me/submissions/b4b7da2a-8b99-4f2b-b059-b59cddf94b68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_surjective_algebraMap_localization_of_henselian

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
    (q : Ideal S) [q.IsMaximal] : Module.Finite R (Localization.AtPrime q) :=
  .of_surjective (IsScalarTower.toAlgHom R S _).toLinearMap
    (surjective_algebraMap_localization_of_henselian R q)
end GlobalTheory
