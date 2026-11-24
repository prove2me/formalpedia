-- Prove2me | solution 1 for GlobalTheory.ConormalDer.exists_derivation_cotangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:20.272947+00:00
-- url     : https://prove2.me/submissions/ecd0f0eb-8164-49c7-b48b-cfa3883bf36f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationExtendingCotangentForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ConormalDer
namespace GlobalTheory.ConormalDer
theorem _root_.solution (R B : Type) [CommRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] [Algebra.FormallySmooth R (ResidueField B)] :
    ∃ D : B →ₗ[R] CotangentSpace B, (∀ a b, D (a * b) = a • D b + b • D a) ∧
      ∀ t : maximalIdeal B, D t = (maximalIdeal B).toCotangent t := by
  set m := maximalIdeal B with hm
  let π : (B ⧸ m ^ 2) →ₐ[R] ResidueField B :=
    Ideal.Quotient.liftₐ (m ^ 2) (IsScalarTower.toAlgHom R B (ResidueField B)) fun a ha =>
      (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha)
  have hπ : ∀ a, π (Ideal.Quotient.mk _ a) = residue B a := fun _ => rfl
  have hsurj : Function.Surjective π := fun y => by
    obtain ⟨a, rfl⟩ := residue_surjective y
    exact ⟨_, hπ a⟩
  have hker : ∀ z, π z = 0 → z ∈ m.cotangentIdeal := fun z hz => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact Ideal.mk_mem_cotangentIdeal.2 ((residue_eq_zero_iff a).1 hz)
  have hnil : IsNilpotent (RingHom.ker (π : (B ⧸ m ^ 2) →+* ResidueField B)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← m.cotangentIdeal_square]
    exact Ideal.pow_right_mono (fun z hz => hker z hz) 2
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R (ResidueField B)) π hsurj hnil
  have hs : ∀ y, π (s y) = y := fun y =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ y
  have hmem : ∀ a, Ideal.Quotient.mk _ a - s (residue B a) ∈ m.cotangentIdeal := fun a =>
    hker _ (by rw [map_sub, hs, hπ, sub_self])
  let D : B → CotangentSpace B := fun a => m.cotangentEquivIdeal.symm ⟨_, hmem a⟩
  have hD : ∀ a, m.cotangentToQuotientSquare (D a) = Ideal.Quotient.mk _ a - s (residue B a) :=
    fun a => by
      rw [← Ideal.cotangentEquivIdeal_apply]
      simp only [D, LinearEquiv.apply_symm_apply]
  have hinj := m.cotangentToQuotientSquare_injective
  have hsq : ∀ a b, (Ideal.Quotient.mk _ a - s (residue B a)) *
      (Ideal.Quotient.mk _ b - s (residue B b)) = 0 := fun a b => by
    have := Ideal.mul_mem_mul (hmem a) (hmem b)
    rwa [← pow_two, m.cotangentIdeal_square, Ideal.mem_bot] at this
  have hsm : ∀ (a : B) (z : B ⧸ m ^ 2), a • z = Ideal.Quotient.mk _ a * z := fun a z =>
    Algebra.smul_def a z
  have hmul : ∀ a b, D (a * b) = a • D b + b • D a := fun a b => by
    apply hinj
    rw [map_add, map_smul, map_smul, hD, hD, hD, hsm, hsm, map_mul, map_mul, map_mul]
    linear_combination (-1 : B ⧸ m ^ 2) * hsq a b
  have hR : ∀ c : R, D (algebraMap R B c) = 0 := fun c => by
    apply hinj
    rw [hD, map_zero, sub_eq_zero]
    exact (s.commutes c).symm
  refine ⟨⟨⟨D, fun a b => ?_⟩, fun c a => ?_⟩, hmul, fun t => ?_⟩
  · apply hinj
    rw [map_add, hD, hD, hD, map_add, map_add, map_add]
    ring
  · show D (c • a) = c • D a
    rw [Algebra.smul_def, hmul, hR, smul_zero, add_zero, algebraMap_smul]
  · apply hinj
    show m.cotangentToQuotientSquare (D t) = _
    rw [hD, (residue_eq_zero_iff _).2 t.2, map_zero, sub_zero, Ideal.toCotangent_to_quotient_square]
    rfl
end GlobalTheory.ConormalDer
