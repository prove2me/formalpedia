-- Prove2me | solution 1 for GlobalTheory.EtaleFibre.encard_points_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:55:25.115145+00:00
-- url     : https://prove2.me/submissions/70486ea8-663f-4caf-b2c6-f33a70128e5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleFibreEmbeddingsCard
import Theorems.Thm_GlobalTheory_EtaleFibre_card_algHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaleFibre
namespace GlobalTheory.EtaleFibre
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] (f : A →+* B), f.Finite → f.Etale → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (letI := f.toAlgebra; Module.finrank A B : ℕ) := by
  intro A B _ _ _ f hf he φ
  letI := f.toAlgebra
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hf
  haveI : Algebra.Etale A B := he
  obtain ⟨hfin, hcard⟩ := card_algHom A B ℂ
  let e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ) :=
    { toFun := fun ψ => { ψ.1 with commutes' := fun a => RingHom.congr_fun ψ.2 a }
      invFun := fun ψ => ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : {ψ : B →+* ℂ | ψ.comp f = φ}.Finite := Finite.of_equiv _ e.symm
  rw [← hs.cast_ncard_eq, ← Nat.card_coe_set_eq, Nat.card_congr e, hcard]
end GlobalTheory.EtaleFibre
