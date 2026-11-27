-- Prove2me | solution 2 for GlobalTheory.charPowPrimeOrder_embeddings_differ_by_coprime_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:07.989712+00:00
-- url     : https://prove2.me/submissions/34b433e6-ede3-43eb-9963-461ced0f9096

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
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] (C : Type) [Field C] [CharZero C] (l n : ℕ), l.Prime →
      ∀ (ψ : Γ →* Cˣ), (∀ g, ψ g ^ (l ^ n) = 1) → ∀ e e' : C →+* ℂ,
        ∃ a : ℕ, Nat.Coprime a l ∧ ∀ g, e' ((ψ g : Cˣ) : C) = e (((ψ g ^ a : Cˣ)) : C) := by
  intro Γ _ C _ _ l n hl ψ hψ e e'
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity (l ^ n) C)
  set u : Cˣ := (ζ : Cˣ) with hu
  have hul : u ^ (l ^ n) = 1 := (mem_rootsOfUnity _ _).mp ζ.2
  set k := orderOf u with hk
  have hkd : k ∣ l ^ n := orderOf_dvd_of_pow_eq_one hul
  have hk0 : 0 < k := Nat.pos_of_ne_zero (fun h => by
    rw [h] at hkd; exact (NeZero.ne (l ^ n)) (Nat.eq_zero_of_zero_dvd hkd))
  haveI : NeZero k := ⟨hk0.ne'⟩
  have hpu : IsPrimitiveRoot (u : C) k := IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf u)
  have h1 : IsPrimitiveRoot (e (u : C)) k := hpu.map_of_injective e.injective
  have h2 : IsPrimitiveRoot (e' (u : C)) k := hpu.map_of_injective e'.injective
  obtain ⟨i, hik, hi⟩ := h1.eq_pow_of_pow_eq_one h2.pow_eq_one
  have hic : i.Coprime k := (h1.pow_iff_coprime hk0 i).mp (by rw [hi]; exact h2)
  refine ⟨i + k, ?_, ?_⟩
  · have hc : (i + k).Coprime k := by simpa using hic
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    intro hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hl).mp hkd
    rcases m with _ | m
    · simp at hm
      have : i = 0 := by omega
      subst this
      rw [hm] at hdvd
      exact hl.one_lt.ne' (Nat.dvd_one.mp (by simpa using hdvd))
    · have hlk : l ∣ k := by rw [hm]; exact dvd_pow_self l (Nat.succ_ne_zero m)
      have := Nat.Coprime.coprime_dvd_left hdvd hc
      have := Nat.Coprime.coprime_dvd_right hlk this
      exact hl.one_lt.ne' (by simpa using this)
  · have hEu : e' (u : C) = e (u : C) ^ (i + k) := by
      rw [pow_add, hi, h1.pow_eq_one, mul_one]
    let E : Cˣ →* ℂˣ := Units.map (e : C →* ℂ)
    let E' : Cˣ →* ℂˣ := Units.map (e' : C →* ℂ)
    have hEu' : E' u = E u ^ (i + k) := by
      ext; simp [E, E', hEu]
    intro g
    have hmem : ψ g ∈ rootsOfUnity (l ^ n) C := (mem_rootsOfUnity _ _).mpr (hψ g)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hζ ⟨ψ g, hmem⟩)
    have hj' : u ^ j = ψ g := by
      have := congrArg Subtype.val hj
      simpa [hu] using this
    have key : E' (ψ g) = E (ψ g ^ (i + k)) := by
      rw [← hj', map_zpow, map_pow, map_zpow, hEu', ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
        ← _root_.zpow_mul, mul_comm]
    have := congrArg Units.val key
    simpa [E, E'] using this
end GlobalTheory
