-- Prove2me | solution 1 for Ideal.eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6c5189ec-beea-57a0-b125-78ef7d787f36

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {B : Type*} [CommRing B] [IsNoetherianRing B] {π : B} {Q Q' : Ideal B}
    [Q.IsPrime] [Q'.IsPrime] (hle : Q' ≤ Q) (hπ : π ∈ Q')
    (h : ∀ p : Ideal B, p.IsPrime → p ≤ Q → (p ∈ minimalPrimes B ↔ π ∉ p)) : Q' = Q := by
  classical
  by_contra hne
  have hlt : Q' < Q := lt_of_le_of_ne hle hne

  have h0 : ∀ p : Ideal B, p.IsPrime → p ≤ Q → π ∈ p → p.height ≠ 0 := fun p hp hpQ hπp hh =>
    ((h p hp hpQ).mp (Ideal.height_eq_zero_iff.mp hh)) hπp

  have hlow : ∀ p q : Ideal B, p.IsPrime → q.IsPrime → q < p → p.height ≤ 1 → q.height = 0 := by
    intro p q hp hq hqp hp1
    have := (Ideal.height_le_iff (p := p) (n := 1)).mp (by exact_mod_cast hp1) q hq hqp
    exact ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast this)

  let S : Set (Ideal B) := minimalPrimes B ∪ (Ideal.span {π}).minimalPrimes
  have hSfin : S.Finite :=
    Set.Finite.union (minimalPrimes.finite_of_isNoetherianRing B)
      (Ideal.finite_minimalPrimes_of_isNoetherianRing B _)
  have hSprime : ∀ p ∈ S, p.IsPrime := by
    rintro p (hp | hp)
    exacts [hp.1.1, hp.1.1]
  have hSht : ∀ p ∈ S, p.height ≤ 1 := by
    rintro p (hp | hp)
    · haveI := hp.1.1
      rw [Ideal.height_eq_zero_iff.mpr hp]
      exact bot_le
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hp

  have hQS : ∀ p ∈ S, ¬ Q ≤ p := by
    intro p hpS hQp
    haveI := hSprime p hpS
    exact h0 Q' ‹_› hle hπ (hlow p Q' ‹_› ‹_› (lt_of_lt_of_le hlt hQp) (hSht p hpS))

  obtain ⟨x, hxQ, hxS⟩ : ∃ x ∈ Q, ∀ p ∈ S, x ∉ p := by
    have key : ¬ ((Q : Set B) ⊆ ⋃ p ∈ (↑hSfin.toFinset : Set (Ideal B)), ((id p : Ideal B) : Set B)) := by
      rw [Ideal.subset_union_prime (R := B) (s := hSfin.toFinset) (f := id) ⊥ ⊥
        (fun p hp _ _ => hSprime p (hSfin.mem_toFinset.mp hp))]
      rintro ⟨p, hp, hQp⟩
      exact hQS p (hSfin.mem_toFinset.mp hp) hQp
    rw [Set.not_subset] at key
    obtain ⟨x, hxQ, hx⟩ := key
    refine ⟨x, hxQ, fun p hp hxp => hx ?_⟩
    simp only [Set.Finite.coe_toFinset, id, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    exact ⟨p, hp, hxp⟩

  obtain ⟨P₁, hP₁, hP₁Q⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := Q)
    ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)
  haveI hP₁pr : P₁.IsPrime := hP₁.1.1
  have hxP₁ : x ∈ P₁ := hP₁.1.2 (Ideal.mem_span_singleton_self x)
  have hP₁ht : P₁.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP₁
  have hπP₁ : π ∈ P₁ := by
    by_contra hπP₁
    exact hxS P₁ (Or.inl ((h P₁ hP₁pr hP₁Q).mpr hπP₁)) hxP₁

  obtain ⟨P₂, hP₂, hP₂P₁⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {π}) (J := P₁)
    ((Ideal.span_singleton_le_iff_mem _).mpr hπP₁)
  haveI hP₂pr : P₂.IsPrime := hP₂.1.1
  have hπP₂ : π ∈ P₂ := hP₂.1.2 (Ideal.mem_span_singleton_self π)
  have hlt₂ : P₂ < P₁ := lt_of_le_of_ne hP₂P₁ fun e => hxS P₂ (Or.inr hP₂) (e ▸ hxP₁)
  exact h0 P₂ hP₂pr (hP₂P₁.trans hP₁Q) hπP₂ (hlow P₁ P₂ hP₁pr hP₂pr hlt₂ hP₁ht)

end S_Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem
end P2MW
export P2MW.S_Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem (solution)
