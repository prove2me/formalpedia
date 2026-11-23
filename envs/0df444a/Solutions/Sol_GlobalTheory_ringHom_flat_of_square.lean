-- Prove2me | solution 1 for GlobalTheory.ringHom_flat_of_square
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:03.643843+00:00
-- url     : https://prove2.me/submissions/7ceaebfb-c7bb-4354-ad37-40fa17772818

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ringHom_flat_of_comp_faithfullyFlat
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
theorem _root_.solution {φ : A →+* B} {φ' : A' →+* B'} {α : A →+* A'} {β : B →+* B'}
    (hsq : φ'.comp α = β.comp φ) (hα : α.Flat) (hβ : β.FaithfullyFlat) (hφ' : φ'.Flat) :
    φ.Flat :=
  ringHom_flat_of_comp_faithfullyFlat hβ (hsq ▸ hα.comp hφ')
end GlobalTheory
