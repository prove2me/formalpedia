-- Prove2me | solution 1 for Leopoldt.exists_algHom_cyclotomicField_of_three_le_finrank
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:50:46.817034+00:00
-- url     : https://prove2.me/submissions/96cf14f4-4ff5-40e2-b154-e41a869120b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LeopoldtDefect
import Theorems.Thm_Leopoldt_exists_algHom_cyclotomicField_of_isCyclic_primePow
import Theorems.Thm_NumberField_exists_algHom_cyclotomicField_of_sup
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.Algebra.Algebra.Hom.Rat

open NumberField

namespace KWC

open Subgroup

lemma inf_eq_bot_of_prime {G : Type*} [Group G] [Finite G] (H : Subgroup G) {y : G} {q : ℕ}
    (hq : q.Prime) (hy : orderOf y = q) (hyH : y ∉ H) : H ⊓ zpowers y = ⊥ := by
  have hcard : Nat.card (zpowers y) = q := by rw [Nat.card_zpowers, hy]
  have hd : Nat.card ↥(H ⊓ zpowers y) ∣ q := hcard ▸ Subgroup.card_dvd_of_le inf_le_right
  rcases hq.eq_one_or_self_of_dvd _ hd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exfalso
    have heq : H ⊓ zpowers y = zpowers y :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hcard])
    exact hyH ((heq ▸ (inf_le_left : H ⊓ zpowers y ≤ H)) (mem_zpowers y))

lemma inf_eq_bot_of_coprime {G : Type*} [Group G] [Finite G] {a b : G}
    (h : Nat.Coprime (orderOf a) (orderOf b)) : zpowers a ⊓ zpowers b = ⊥ := by
  have h1 : Nat.card ↥(zpowers a ⊓ zpowers b) ∣ orderOf a :=
    Nat.card_zpowers a ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(zpowers a ⊓ zpowers b) ∣ orderOf b :=
    Nat.card_zpowers b ▸ Subgroup.card_dvd_of_le inf_le_right
  exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h) h2)

/-- A finite abelian group which is not cyclic of prime-power order has two nontrivial
subgroups with trivial intersection. -/
theorem exists_inf_eq_bot {G : Type*} [Group G] [Finite G] (hcomm : ∀ a b : G, a * b = b * a)
    (h : ¬ (IsCyclic G ∧ ∃ p k : ℕ, p.Prime ∧ Nat.card G = p ^ k)) :
    ∃ H₁ H₂ : Subgroup G, H₁ ≠ ⊥ ∧ H₂ ≠ ⊥ ∧ H₁ ⊓ H₂ = ⊥ := by
  letI : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  by_cases hcyc : IsCyclic G
  · -- the order is not a prime power: two distinct primes divide it
    have hN : ¬ ∃ p k : ℕ, p.Prime ∧ Nat.card G = p ^ k := fun h' => h ⟨hcyc, h'⟩
    have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hN1 : Nat.card G ≠ 1 := fun h1 => hN ⟨2, 0, Nat.prime_two, by rw [h1]; rfl⟩
    set p := (Nat.card G).minFac
    have hp : p.Prime := Nat.minFac_prime hN1
    have hpd : p ∣ Nat.card G := Nat.minFac_dvd _
    obtain ⟨q, hq, hqd, hqp⟩ : ∃ q, q.Prime ∧ q ∣ Nat.card G ∧ q ≠ p := by
      by_contra hc
      push Not at hc
      exact hN ⟨p, _, hp, Nat.eq_prime_pow_of_unique_prime_dvd hN0 (fun hd hdd => hc _ hd hdd)⟩
    haveI := Fact.mk hp
    haveI := Fact.mk hq
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpd
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' q hqd
    refine ⟨zpowers a, zpowers b, ?_, ?_, inf_eq_bot_of_coprime ?_⟩
    · rw [Ne, zpowers_eq_bot]; rintro rfl; rw [orderOf_one] at ha; exact hp.one_lt.ne ha
    · rw [Ne, zpowers_eq_bot]; rintro rfl; rw [orderOf_one] at hb; exact hq.one_lt.ne hb
    · rw [ha, hb]; exact (Nat.coprime_primes hp hq).mpr hqp.symm
  · obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (Monoid.ExponentExists.of_finite (G := G))
    set H₁ := zpowers g
    have hH₁ : ∃ x, x ∉ H₁ := by
      by_contra hc
      push Not at hc
      exact hcyc ⟨g, fun x => Subgroup.mem_zpowers_iff.mp (hc x)⟩
    classical
    have hex : ∃ n, ∃ x, x ∉ H₁ ∧ orderOf x = n := by
      obtain ⟨x, hx⟩ := hH₁; exact ⟨_, x, hx, rfl⟩
    obtain ⟨x, hx, hxn⟩ := Nat.find_spec hex
    set n := Nat.find hex
    have hmin : ∀ z, z ∉ H₁ → n ≤ orderOf z := fun z hz => Nat.find_min' hex ⟨z, hz, rfl⟩
    have hn1 : n ≠ 1 := by
      intro h1; rw [h1, orderOf_eq_one_iff] at hxn; exact hx (hxn ▸ one_mem _)
    obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd hn1
    haveI := Fact.mk hq
    have hnpos : 0 < n := hxn ▸ orderOf_pos x
    have hxq : x ^ q ∈ H₁ := by
      by_contra hc
      have := hmin _ hc
      rw [orderOf_pow_of_dvd hq.ne_zero (hxn ▸ hqn), hxn] at this
      exact absurd this (not_le.mpr (Nat.div_lt_self hnpos hq.one_lt))
    obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hxq
    -- `q ∣ s`
    obtain ⟨m, hm⟩ := hqn
    have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; omega
    have hdvd : ((q * m : ℕ) : ℤ) ∣ s * (m : ℤ) := by
      have h1 : g ^ (s * (m : ℤ)) = 1 := by
        rw [zpow_mul, hs, zpow_natCast, ← pow_mul, ← hm, ← hxn, pow_orderOf_eq_one]
      have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [hg] at h2
      rw [← hm]
      exact dvd_trans (Int.natCast_dvd_natCast.mpr (hxn ▸ Monoid.order_dvd_exponent x)) h2
    have hq_s : (q : ℤ) ∣ s := by
      rw [Nat.cast_mul] at hdvd
      exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hm0) hdvd
    obtain ⟨t, rfl⟩ := hq_s
    set y := x * g ^ (-t)
    have hyq : y ^ q = 1 := by
      rw [mul_pow, ← zpow_natCast (g ^ (-t)), ← zpow_mul, ← hs, ← zpow_add,
        show (q : ℤ) * t + -t * q = 0 by ring, zpow_zero]
    have hyH : y ∉ H₁ := by
      intro hy
      apply hx
      have : x = y * g ^ t := by simp [y, mul_assoc]
      rw [this]
      exact mul_mem hy (zpow_mem (mem_zpowers g) t)
    have hy1 : y ≠ 1 := fun h1 => hyH (h1 ▸ one_mem _)
    refine ⟨H₁, zpowers y, ?_, ?_, inf_eq_bot_of_prime H₁ hq (orderOf_eq_prime hyq hy1) hyH⟩
    · intro hb
      have hg1 : g = 1 := by rw [← zpowers_eq_bot]; exact hb
      have hx1 : orderOf x ∣ 1 := by
        have := Monoid.order_dvd_exponent x
        rwa [← hg, hg1, orderOf_one] at this
      exact hx ((orderOf_eq_one_iff.mp (Nat.dvd_one.mp hx1)) ▸ one_mem _)
    · rw [Ne, zpowers_eq_bot]; exact hy1

end KWC

universe u

namespace KWC

open IntermediateField in
theorem main (n : ℕ) : ∀ (L : Type u) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)], Module.finrank ℚ L = n →
    ∃ m : ℕ, 0 < m ∧ Nonempty (L →ₐ[ℚ] CyclotomicField m ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L _ inst _ _ _ hn
  by_cases hc : IsCyclic (L ≃ₐ[ℚ] L) ∧ ∃ p k : ℕ, p.Prime ∧ Nat.card (L ≃ₐ[ℚ] L) = p ^ k
  · obtain ⟨hcyc, p, k, hp, hcard⟩ := hc
    have cz : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    haveI : NumberField L := ⟨⟩
    exact Leopoldt.exists_algHom_cyclotomicField_of_isCyclic_primePow L p k hp
      (by rw [← IsGalois.card_aut_eq_finrank]; exact hcard)
  · obtain ⟨H₁, H₂, h₁, h₂, hinf⟩ := exists_inf_eq_bot (fun a b => mul_comm' a b) hc
    haveI : IsAbelianGalois ℚ L := ⟨⟩
    have hdeg : ∀ H : Subgroup (L ≃ₐ[ℚ] L), H ≠ ⊥ → Module.finrank ℚ (fixedField H) < n := by
      intro H hH
      have h1 : 1 < Nat.card H := (Subgroup.one_lt_card_iff_ne_bot H).mpr hH
      have h2 := Module.finrank_mul_finrank ℚ (fixedField H) L
      rw [finrank_fixedField_eq_card, hn] at h2
      have h3 : 0 < Module.finrank ℚ (fixedField H) := Module.finrank_pos
      rw [← h2]
      exact lt_mul_of_one_lt_right h3 h1
    have hemb : ∀ H : Subgroup (L ≃ₐ[ℚ] L), H ≠ ⊥ →
        ∃ m : ℕ, 0 < m ∧ Nonempty (fixedField H →ₐ[ℚ] CyclotomicField m ℚ) := fun H hH => by
      obtain ⟨m, hm, ⟨f⟩⟩ := @ih _ (hdeg H hH) (fixedField H) _ (fixedField H).algebra' _ _ _ rfl
      exact ⟨m, hm, ⟨(f : fixedField H →+* CyclotomicField m ℚ).toRatAlgHom⟩⟩
    have htop : fixedField H₁ ⊔ fixedField H₂ = ⊤ := by
      have : (fixedField H₁ ⊔ fixedField H₂).fixingSubgroup = ⊥ := by
        rw [fixingSubgroup_sup, fixingSubgroup_fixedField, fixingSubgroup_fixedField, hinf]
      rw [← IsGalois.fixedField_fixingSubgroup (fixedField H₁ ⊔ fixedField H₂), this,
        fixedField_bot]
    obtain ⟨m, hm, ⟨f⟩⟩ := NumberField.exists_algHom_cyclotomicField_of_sup _ _
      (by obtain ⟨m, hm, ⟨f⟩⟩ := hemb H₁ h₁
          exact ⟨m, hm, ⟨(f : fixedField H₁ →+* CyclotomicField m ℚ).toRatAlgHom⟩⟩)
      (by obtain ⟨m, hm, ⟨f⟩⟩ := hemb H₂ h₂
          exact ⟨m, hm, ⟨(f : fixedField H₂ →+* CyclotomicField m ℚ).toRatAlgHom⟩⟩)
    let e : L →+* ↥(fixedField H₁ ⊔ fixedField H₂) :=
      { toFun := fun x => ⟨x, by rw [htop]; exact mem_top⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact ⟨m, hm, ⟨((f : _ →+* CyclotomicField m ℚ).comp e).toRatAlgHom⟩⟩

end KWC

theorem solution (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] [IsMulCommutative (K ≃ₐ[ℚ] K)] (hK : 3 ≤ Module.finrank ℚ K) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) :=
  KWC.main _ K rfl
