-- Prove2me | solution 1 for GlobalTheory.LocalFlatMax.lTensor_injective_of_pow_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:03:00.710984+00:00
-- url     : https://prove2.me/submissions/30103fe1-14a8-44ff-a9a1-4f9ca9421029

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomFlatOfCompFlatOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_LocalFlatMax_lTensor_injective_of_smul_le
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap IsLocalRing
open GlobalTheory
open GlobalTheory.LocalFlatMax
universe u
variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
namespace GlobalTheory.LocalFlatMax
theorem _root_.solution (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (n : ℕ) (N : Submodule A F)
    (hN : I ^ n • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by
  induction n generalizing N with
  | zero => exact lTensor_injective_of_smul_le I h N (le_top.trans (by simpa using hN))
  | succ n ih =>
    let N' : Submodule A F := N ⊔ I ^ n • ⊤
    have h1 := ih N' le_sup_right
    have h2 := lTensor_injective_of_smul_le I h (N.comap N'.subtype) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_subtype_top,
        Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ']
      exact sup_le Submodule.smul_le_right hN)
    have : N.subtype = N'.subtype ∘ₗ (N.comap N'.subtype).subtype ∘ₗ
        (Submodule.comapSubtypeEquivOfLe (le_sup_left : N ≤ N')).symm.toLinearMap := by
      ext
      rfl
    rw [this, lTensor_comp, lTensor_comp]
    exact h1.comp (h2.comp (LinearEquiv.lTensor M _).injective)
end GlobalTheory.LocalFlatMax
