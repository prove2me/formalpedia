-- Prove2me | solution 1 for IsRegularLocalRing.exists_notMem_sq_charZero_quotient_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/aab9d79d-5521-583d-a79b-709655c6253d

import Mathlib
import Theorems.Thm_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_notMem_sq_charZero_quotient_span_singleton
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open IsLocalRing

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsRegularLocalRing R] [IsRegularRing R] [CharZero R] (hd : 2 ≤ ringKrullDim R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ x ≠ 0 ∧ CharZero (R ⧸ Ideal.span {x}) := by
  classical
  haveI : UniqueFactorizationMonoid R := IsRegularRing.uniqueFactorizationMonoid_of_isLocalRing R

  set p : ℕ := ringChar (ResidueField R) with hpdef
  set T : Set (Ideal R) := (Ideal.span {(p : R)}).minimalPrimes with hT
  have hTfin : T.Finite := (Ideal.span {(p : R)}).finite_minimalPrimes_of_isNoetherianRing

  have hTle : ∀ P ∈ T, P.height ≤ 1 := fun P hP =>
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {(p : R)}) P hP
  have hTne : ∀ P ∈ T, ¬ maximalIdeal R ≤ P := by
    intro P hP hle
    have hPne : P ≠ ⊤ := hP.1.1.ne_top
    have hEq : maximalIdeal R = P := (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hPne hle
    have h1 := hTle P hP
    rw [← hEq] at h1
    have hdim1 : ringKrullDim R ≤ 1 := by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact_mod_cast h1
    exact absurd (hd.trans hdim1) (by norm_num)
  have hmm : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := by
    intro hle
    have hbot : maximalIdeal R = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
        (IsNoetherian.noetherian _) ?_ ?_
      · rw [Ideal.smul_eq_mul, ← pow_two]; exact hle
      · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    have hF : IsField R := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot
    have h0 := ringKrullDim_eq_zero_of_isField hF
    rw [h0] at hd
    exact absurd hd (by norm_num)

  obtain ⟨x, hxm, hxU⟩ : ∃ x ∈ (maximalIdeal R : Set R),
      x ∉ ⋃ i ∈ (↑(insert (maximalIdeal R ^ 2) hTfin.toFinset) : Set (Ideal R)), ((i : Ideal R) : Set R) := by
    rw [← Set.not_subset]
    intro hsub
    have := (Ideal.subset_union_prime (maximalIdeal R ^ 2) (maximalIdeal R ^ 2) (f := fun i : Ideal R => i)
      (s := insert (maximalIdeal R ^ 2) hTfin.toFinset) (fun i hi hia _ => ?_)).mp hsub
    · obtain ⟨i, hi, hle⟩ := this
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hmm hle
      · exact hTne i (hTfin.mem_toFinset.mp hi) hle
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact absurd rfl hia
      · exact (hTfin.mem_toFinset.mp hi).1.1
  simp only [Set.mem_iUnion, exists_prop, not_exists, not_and, Finset.coe_insert, Set.mem_insert_iff,
    Set.Finite.coe_toFinset] at hxU
  have hx2 : x ∉ maximalIdeal R ^ 2 := fun h => by
    have := hxU (maximalIdeal R ^ 2)
    tauto
  have hxT : ∀ P ∈ T, x ∉ P := fun P hP h => by
    have := hxU P
    tauto
  have hx0 : x ≠ 0 := fun h => hx2 (h ▸ Submodule.zero_mem _)

  have hxu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hxm
  have hirr : Irreducible x := by
    refine ⟨hxu, fun a b hab => ?_⟩
    by_contra h
    push Not at h
    apply hx2
    rw [hab, pow_two]
    exact Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal a).mpr h.1) ((IsLocalRing.mem_maximalIdeal b).mpr h.2)
  haveI hP : (Ideal.span {x}).IsPrime := (Ideal.span_singleton_prime hx0).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)

  have hpx : p ≠ 0 → (p : R) ∉ Ideal.span {x} := by
    intro hp0 hpin
    have hle : Ideal.span {(p : R)} ≤ Ideal.span {x} := (Ideal.span_singleton_le_iff_mem _).mpr hpin
    obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le hle
    haveI := hPmin.1.1
    have hxP := hxT P hPmin
    have hlt : P < Ideal.span {x} := lt_of_le_of_ne hPle (fun h => hxP (h.symm ▸ Ideal.mem_span_singleton_self x))
    have h1 : (Ideal.span {x}).height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) (Ideal.span {x})
        (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _)
    have h0 : P.height = 0 := by
      have := (Ideal.height_strict_mono_of_isPrime hlt).trans_le h1
      exact ENat.lt_one_iff_eq_zero.mp this
    have hPbot : P = ⊥ := by
      have hmem := (Ideal.height_eq_zero_iff.mp h0)
      have : (⊥ : Ideal R).minimalPrimes = {⊥} := Ideal.minimalPrimes_eq_subsingleton_self
      change P ∈ (⊥ : Ideal R).minimalPrimes at hmem
      rw [this] at hmem
      exact hmem
    have hpP : (p : R) ∈ P := hPmin.1.2 (Ideal.mem_span_singleton_self _)
    rw [hPbot, Ideal.mem_bot, Nat.cast_eq_zero] at hpP
    exact hp0 hpP
  refine ⟨x, hxm, hx2, hx0, ?_⟩

  haveI : IsDomain (R ⧸ Ideal.span {x}) := (Ideal.Quotient.isDomain_iff_prime _).mpr hP
  refine (CharZero.charZero_iff_forall_prime_ne_zero (R ⧸ Ideal.span {x})).mpr fun ℓ hℓ hℓ0 => ?_

  have hℓx : (ℓ : R) ∈ Ideal.span {x} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hℓ0
  have hℓm : (ℓ : R) ∈ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).mpr hxm hℓx
  have hℓk : (ℓ : ResidueField R) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]; exact hℓm
  have hpl : p ∣ ℓ := (CharP.cast_eq_zero_iff (ResidueField R) p ℓ).mp hℓk
  by_cases hp0 : p = 0
  · rw [hp0] at hpl
    exact hℓ.ne_zero (Nat.eq_zero_of_zero_dvd hpl)
  · have hpprime : p.Prime := (CharP.char_is_prime_or_zero (ResidueField R) p).resolve_right hp0
    have hpeq : p = ℓ := (Nat.prime_dvd_prime_iff_eq hpprime hℓ).mp hpl
    exact hpx hp0 (hpeq ▸ hℓx)

end S_IsRegularLocalRing_exists_notMem_sq_charZero_quotient_span_singleton
end P2MW
export P2MW.S_IsRegularLocalRing_exists_notMem_sq_charZero_quotient_span_singleton (solution)
