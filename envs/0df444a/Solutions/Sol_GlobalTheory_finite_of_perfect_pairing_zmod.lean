-- Prove2me | solution 1 for GlobalTheory.finite_of_perfect_pairing_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:22.3632+00:00
-- url     : https://prove2.me/submissions/61a0fdcc-d2c1-46ec-a93a-5ea8a2282291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmod
import Theorems.Thm_GlobalTheory_mk_lt_mk_addMonoidHom_zmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function Cardinal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A]
    [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C]
    [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C),
    Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by
  intro n _ A B C _ _ _ _ _ _ _ b ⟨e⟩ hb hbf
  have key : ∀ (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [AddCommGroup Y]
      [Module (ZMod n) Y] (c : X →ₗ[ZMod n] Y →ₗ[ZMod n] C), Bijective c.flip → Infinite X →
      #X < #Y := by
    intro X Y _ _ _ _ c hc hX
    have h1 : #Y = #(X →+ ZMod n) := by
      have e1 := (LinearEquiv.ofBijective c.flip hc).toEquiv
      have e2 : (X →ₗ[ZMod n] C) ≃ (X →ₗ[ZMod n] ZMod n) :=
        { toFun := fun g => e.toLinearMap ∘ₗ g
          invFun := fun g => e.symm.toLinearMap ∘ₗ g
          left_inv := fun g => by ext; simp
          right_inv := fun g => by ext; simp }
      have e3 := (AddMonoidHom.toZModLinearMapEquiv n (M := X) (M₁ := ZMod n)).toEquiv.symm
      exact (e1.trans (e2.trans e3)).cardinal_eq
    rw [h1]
    refine mk_lt_mk_addMonoidHom_zmod n X (fun x => ?_) (NeZero.ne n) hX
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have hbff : Bijective b.flip.flip := by simpa using hb
  have hA : Finite A := by
    by_contra hA
    rw [not_finite_iff_infinite] at hA
    have h1 := key A B b hbf hA
    haveI : Infinite B := Cardinal.infinite_iff.mpr ((aleph0_le_mk A).trans h1.le)
    exact lt_asymm h1 (key B A b.flip hbff inferInstance)
  have hB : Finite B := by
    by_contra hB
    rw [not_finite_iff_infinite] at hB
    have h1 := key B A b.flip hbff hB
    haveI : Infinite A := Cardinal.infinite_iff.mpr ((aleph0_le_mk B).trans h1.le)
    exact not_finite A
  exact ⟨hA, hB⟩
end GlobalTheory
