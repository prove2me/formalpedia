-- Prove2me | solution 1 for GlobalTheory.ringHom_flat_of_comp_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:34.993965+00:00
-- url     : https://prove2.me/submissions/ab77dfac-dfe9-40eb-8311-374d73a20074

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
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
theorem _root_.solution {φ : A →+* B} {β : B →+* B'}
    (hβ : β.FaithfullyFlat) (h : (β.comp φ).Flat) : φ.Flat := by
  algebraize [φ, β, β.comp φ]
  rw [RingHom.Flat, Module.Flat.iff_lTensor_injective']
  intro J
  change Function.Injective (AlgebraTensorModule.lTensor B B J.subtype)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective B B']
  have : (LinearMap.lTensor B' (AlgebraTensorModule.lTensor B B J.subtype)) =
      (AlgebraTensorModule.cancelBaseChange A B B B' A).symm.toLinearMap ∘ₗ
        AlgebraTensorModule.lTensor B B' J.subtype ∘ₗ
          (AlgebraTensorModule.cancelBaseChange A B B B' J).toLinearMap := by
    ext
    simp
  rw [this]
  simpa using Module.Flat.lTensor_preserves_injective_linearMap (M := B') J.subtype
    J.injective_subtype
end GlobalTheory
