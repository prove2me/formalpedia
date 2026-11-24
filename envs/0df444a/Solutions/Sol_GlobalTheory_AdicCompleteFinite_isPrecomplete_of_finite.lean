-- Prove2me | solution 1 for GlobalTheory.AdicCompleteFinite.isPrecomplete_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:55:23.324598+00:00
-- url     : https://prove2.me/submissions/eb2dc708-2054-45d2-96bd-80d1eb7af841

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsAdicCompleteOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.AdicCompleteFinite
namespace GlobalTheory.AdicCompleteFinite
theorem _root_.solution {R M : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) a (AdicCompletion.of I M m)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
end GlobalTheory.AdicCompleteFinite
