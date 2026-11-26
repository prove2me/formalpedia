-- Prove2me | solution 1 for GlobalTheory.charPowPrimeOrder_embeddings_differ_by_coprime_power
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:46:50.902051+00:00
-- url     : https://prove2.me/submissions/df48ce2c-8b4c-4aa7-8704-f9a37a6729f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharPowPrimeOrderEmbeddingsDifferByCoprimePower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped TensorProduct Classical
open GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] (C : Type) [Field C] [CharZero C] (l n : ℕ), l.Prime →
      ∀ (ψ : Γ →* Cˣ), (∀ g, ψ g ^ (l ^ n) = 1) → ∀ e e' : C →+* ℂ,
        ∃ a : ℕ, Nat.Coprime a l ∧ ∀ g, e' ((ψ g : Cˣ) : C) = e (((ψ g ^ a : Cˣ)) : C) := by
  intro Γ _ C _ _ l n hl ψ hψ e e'
  classical
  have hN : 0 < l ^ n := pow_pos hl.pos n
  -- the image of ψ is a finite, hence cyclic, group of roots of unity
  have hle : ψ.range ≤ rootsOfUnity (l ^ n) C := by
    rintro x ⟨g, rfl⟩
    rw [mem_rootsOfUnity]; exact hψ g
  haveI : NeZero (l ^ n) := ⟨hN.ne'⟩
  haveI : Finite ψ.range := Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  haveI : IsCyclic ψ.range := isCyclic_of_subgroup_isDomain ((Units.coeHom C).comp ψ.range.subtype)
    (Units.val_injective.comp Subtype.val_injective)
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := ψ.range)
  set ζ : Cˣ := (z : Cˣ) with hζ
  set m := orderOf ζ with hm
  have hm_dvd : m ∣ l ^ n := by
    obtain ⟨g, hg⟩ := z.2
    exact orderOf_dvd_of_pow_eq_one (by rw [hζ, ← hg]; exact hψ g)
  have hm0 : m ≠ 0 := fun h => by
    rw [h, zero_dvd_iff] at hm_dvd; exact hN.ne' hm_dvd
  have hprimC : IsPrimitiveRoot ((ζ : Cˣ) : C) m := by
    have : orderOf ((ζ : Cˣ) : C) = m := orderOf_units
    rw [← this]; exact IsPrimitiveRoot.orderOf _
  have hp1 : IsPrimitiveRoot (e ((ζ : Cˣ) : C)) m := hprimC.map_of_injective e.injective
  have hp2 : IsPrimitiveRoot (e' ((ζ : Cˣ) : C)) m := hprimC.map_of_injective e'.injective
  haveI : NeZero m := ⟨hm0⟩
  obtain ⟨i, _, hi⟩ := hp1.eq_pow_of_pow_eq_one hp2.pow_eq_one
  have hcop : Nat.Coprime i m := by
    refine (hp1.pow_iff_coprime (Nat.pos_of_ne_zero hm0) i).1 ?_
    rw [hi]; exact hp2
  have key : ∃ a : ℕ, Nat.Coprime a l ∧ e' ((ζ : Cˣ) : C) = (e ((ζ : Cˣ) : C)) ^ a := by
    by_cases hm1 : m = 1
    · refine ⟨1, Nat.coprime_one_left l, ?_⟩
      have h1 : e ((ζ : Cˣ) : C) = 1 := by
        have := hp1.pow_eq_one; rwa [hm1, pow_one] at this
      have h2 : e' ((ζ : Cˣ) : C) = 1 := by
        have := hp2.pow_eq_one; rwa [hm1, pow_one] at this
      rw [h1, h2, one_pow]
    · refine ⟨i, ?_, hi.symm⟩
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hl).1 hm_dvd
      have hk0 : k ≠ 0 := fun h => hm1 (by rw [hk, h, pow_zero])
      rw [hk] at hcop
      exact Nat.Coprime.coprime_dvd_right (dvd_pow_self l hk0) hcop
  obtain ⟨a, ha, haz⟩ := key
  refine ⟨a, ha, fun g => ?_⟩
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  have hg : (⟨ψ g, g, rfl⟩ : ψ.range) ∈ Submonoid.powers z :=
    hfin.mem_powers_iff_mem_zpowers.2 (hz _)
  obtain ⟨j, hj⟩ := hg
  have hψg : ψ g = ζ ^ j := by
    have := congrArg (fun x : ψ.range => (x : Cˣ)) hj
    simpa using this.symm
  rw [hψg]
  simp only [Units.val_pow_eq_pow_val, map_pow]
  rw [haz, ← pow_mul, ← pow_mul, Nat.mul_comm]

