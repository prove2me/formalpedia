-- Prove2me | solution 1 for N25.characterField_exists_norm_cover
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:48.704682+00:00
-- url     : https://prove2.me/submissions/b28a7315-3a0c-45e0-8cb4-938c3d9844d2

import Mathlib
import Theorems.Thm_N25_characterField_prime_above_five_unique
import Definitions.Def_N25_CharacterField
import Mathlib.NumberTheory.NumberField.Norm
import Theorems.Thm_N25_characterField_primes_over_seven_count
import Definitions.Def_N25
import Mathlib.NumberTheory.RamificationInertia.Galois
import Theorems.Thm_N25_characterField_small_norm_ideal
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false

noncomputable section

open scoped NumberField nonZeroDivisors

namespace N25

/-- The concrete quintic field has a cover by at most seven ideals for
all nonzero ideals of norm at most 24. -/
theorem _root_.solution :
    ∃ s : Finset (Ideal (𝓞 characterField))⁰, s.card ≤ 7 ∧
      ∀ I : (Ideal (𝓞 characterField))⁰,
        Ideal.absNorm (I : Ideal (𝓞 characterField)) ≤ 24 → I ∈ s := by
  classical
  let a : Set (Ideal (𝓞 characterField))⁰ := {I | Ideal.absNorm (I : Ideal (𝓞 characterField)) = 5}
  let b : Set (Ideal (𝓞 characterField))⁰ := {I | Ideal.absNorm (I : Ideal (𝓞 characterField)) = 7}
  have ha : a.Finite := (Ideal.finite_setOfPred_absNorm_le₀ 24).subset (by intro I hI; change _ = 5 at hI; change _ ≤ 24; omega)
  have hb : b.Finite := (Ideal.finite_setOfPred_absNorm_le₀ 24).subset (by intro I hI; change _ = 7 at hI; change _ ≤ 24; omega)
  have hca : a.ncard ≤ 1 := by
    apply (Set.ncard_le_one ha).mpr
    intro I hI J hJ
    change Ideal.absNorm (I : Ideal (𝓞 characterField)) = 5 at hI
    change Ideal.absNorm (J : Ideal (𝓞 characterField)) = 5 at hJ
    haveI : (I : Ideal (𝓞 characterField)).IsPrime :=
      Ideal.isPrime_of_irreducible_absNorm (by rw [hI]; exact Nat.prime_five)
    haveI : (J : Ideal (𝓞 characterField)).IsPrime :=
      Ideal.isPrime_of_irreducible_absNorm (by rw [hJ]; exact Nat.prime_five)
    apply Subtype.ext
    exact characterField_prime_above_five_unique I J
      (nonZeroDivisors.ne_zero I.property) (nonZeroDivisors.ne_zero J.property)
      (by simpa only [hI, Nat.cast_ofNat] using Ideal.absNorm_mem (I : Ideal (𝓞 characterField)))
      (by simpa only [hJ, Nat.cast_ofNat] using Ideal.absNorm_mem (J : Ideal (𝓞 characterField)))
  have hcb : b.ncard ≤ 5 := by
    apply le_trans ?_ characterField_primes_over_seven_count
    haveI : (Ideal.span {(7 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num : (7 : ℤ) ≠ 0)).mpr (by norm_num)
    refine Set.ncard_le_ncard_of_injOn
      (fun I : (Ideal (𝓞 characterField))⁰ => (I : Ideal (𝓞 characterField))) ?_ ?_ ?_
    · intro I hI
      change Ideal.absNorm (I : Ideal (𝓞 characterField)) = 7 at hI
      have hprime : (I : Ideal (𝓞 characterField)).IsPrime :=
        Ideal.isPrime_of_irreducible_absNorm (by rw [hI]; exact Nat.prime_seven)
      refine ⟨hprime, ⟨?_⟩⟩
      simpa only [hI, Nat.cast_ofNat] using (Ideal.span_singleton_absNorm
        (I := (I : Ideal (𝓞 characterField))) (by rw [hI]; exact Nat.prime_seven))
    · intro I _ J _ hIJ
      exact Subtype.ext hIJ
    · exact Algebra.QuasiFinite.finite_primesOver _
  let t : Set (Ideal (𝓞 characterField))⁰ := ({1} ∪ a) ∪ b
  have ht : t.Finite := ((Set.finite_singleton 1).union ha).union hb
  refine ⟨ht.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card t ht]
    have h₁ := Set.ncard_union_le ({1} : Set (Ideal (𝓞 characterField))⁰) a
    have h₂ := Set.ncard_union_le (({1} : Set (Ideal (𝓞 characterField))⁰) ∪ a) b
    simp only [Set.ncard_singleton] at h₁
    change (({1} ∪ a) ∪ b).ncard ≤ 7
    omega
  · intro I hI
    apply ht.mem_toFinset.mpr
    rcases characterField_small_norm_ideal I hI with h | h | h
    · exact Or.inl (Or.inl (by apply Subtype.ext; simpa using h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

end N25
