-- Prove2me | solution 1 for GlobalTheory.ringHom_flat_of_square_of_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:47.255418+00:00
-- url     : https://prove2.me/submissions/2ad90244-955e-4d4e-a4e5-24c9e470d5ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ringHom_flat_of_square
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
namespace GlobalTheory
theorem _root_.solution [IsLocalRing B] [IsLocalRing B'] {φ : A →+* B}
    {φ' : A' →+* B'} {α : A →+* A'} {β : B →+* B'} [IsLocalHom β]
    (hsq : φ'.comp α = β.comp φ) (hα : α.Flat) (hβ : β.Flat) (hφ' : φ'.Flat) : φ.Flat := by
  refine ringHom_flat_of_square hsq hα ?_ hφ'
  algebraize [β]
  haveI : IsLocalHom (algebraMap B B') := ‹IsLocalHom β›
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom
end GlobalTheory
