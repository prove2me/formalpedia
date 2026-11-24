-- Prove2me | solution 1 for GlobalTheory.nonempty_closure_ringHom_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:02.096658+00:00
-- url     : https://prove2.me/submissions/81cbed85-f0db-421c-878a-38abfc6f2387

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NumberFieldToModPSquared

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] [CharZero K] (O : Subring K) (R : Type) [CommRing R] (ψ : O →+* R) (N : ℕ), 0 < N → IsUnit (N : R) → ∀ (S : Finset K), (∀ s ∈ S, (N : K) * s ∈ O) → Nonempty (Subring.closure (S : Set K) →+* R) := by
  intro K _ _ O R _ ψ N hN hu S hS
  set B := Localization.Away (N : O)
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hunits : ∀ m : Submonoid.powers (N : O), IsUnit (O.subtype m) := by
    rintro ⟨m, k, rfl⟩
    simp only [map_pow, map_natCast]
    exact (isUnit_iff_ne_zero.mpr hNK).pow k
  let φ : B →+* K := IsLocalization.lift (M := Submonoid.powers (N : O)) hunits
  have hφa : ∀ a : O, φ (algebraMap O B a) = (a : K) := fun a => IsLocalization.lift_eq hunits a
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (N : O)) b
    have h1 := congrArg φ (IsLocalization.mk'_spec B a m)
    rw [map_mul, hb, zero_mul, hφa] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    subst ha; exact IsLocalization.mk'_zero _
  have hle : Subring.closure (S : Set K) ≤ φ.range := by
    rw [Subring.closure_le]
    intro s hs
    refine ⟨IsLocalization.mk' B (⟨(N : K) * s, hS s hs⟩ : O) (⟨(N : O), 1, pow_one _⟩ : Submonoid.powers (N : O)), ?_⟩
    have h1 := congrArg φ (IsLocalization.mk'_spec B (⟨(N : K) * s, hS s hs⟩ : O) (⟨(N : O), 1, pow_one _⟩ : Submonoid.powers (N : O)))
    rw [map_mul, hφa, hφa] at h1
    simp only [map_natCast] at h1
    exact mul_right_cancel₀ hNK (h1.trans (mul_comm _ _))
  have hψN : IsUnit (ψ (N : O)) := by rw [map_natCast]; exact hu
  let χ : B →+* R := IsLocalization.Away.lift (N : O) hψN
  let e : B ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict ⟨fun x y h => hinj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  exact ⟨χ.comp (e.symm.toRingHom.comp (Subring.inclusion hle))⟩
end GlobalTheory
