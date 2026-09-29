-- Prove2me | solution 1 for IsLocalRing.exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/831b9fdf-c303-57dd-88f6-ba278ef662c6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add

open IsLocalRing

namespace EngineCoreSol

variable {R : Type*} [CommRing R]

section dimOne

variable [IsLocalRing R]

theorem isNilpotent_mk_of_mem_map {P : Type*} [CommRing P] [Algebra R P]
    {b : R} (hnil : ∀ c ∈ maximalIdeal R, ∃ n : ℕ, b ∣ c ^ n)
    {x : P} (hx : x ∈ (maximalIdeal R).map (algebraMap R P)) :
    IsNilpotent (Ideal.Quotient.mk (Ideal.span {algebraMap R P b}) x) := by
  have hle : (maximalIdeal R).map (algebraMap R P) ≤
      (nilradical (P ⧸ Ideal.span {algebraMap R P b})).comap
        (Ideal.Quotient.mk (Ideal.span {algebraMap R P b})) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨n, c, hc⟩ := hnil a ha
    simp only [Ideal.mem_comap, mem_nilradical]
    refine ⟨n, ?_⟩
    rw [← map_pow, ← map_pow, hc, map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  exact hle hx

theorem exists_mul_self_sub_mem_span_and_sub_mem {P : Type*} [CommRing P] [Algebra R P]
    {b : R} (hb : b ∈ maximalIdeal R) (hnil : ∀ c ∈ maximalIdeal R, ∃ n : ℕ, b ∣ c ^ n)
    (e : P) (he : e * e - e ∈ (maximalIdeal R).map (algebraMap R P)) :
    ∃ x : P, x * x - x ∈ Ideal.span {algebraMap R P b} ∧
      x - e ∈ (maximalIdeal R).map (algebraMap R P) := by
  set I : Ideal P := Ideal.span {algebraMap R P b} with hI
  set J : Ideal P := (maximalIdeal R).map (algebraMap R P) with hJ
  have hIJ : I ≤ J := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hb
  let f : P ⧸ I →+* P ⧸ J := Ideal.Quotient.factor hIJ
  have hf : ∀ z : P, f (Ideal.Quotient.mk I z) = Ideal.Quotient.mk J z := fun z => by
    simp [f]
  have hker : ∀ y ∈ RingHom.ker f, IsNilpotent y := by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hz : z ∈ J := by
      rw [RingHom.mem_ker, hf, Ideal.Quotient.eq_zero_iff_mem] at hy
      exact hy
    exact isNilpotent_mk_of_mem_map hnil hz
  have hidem : IsIdempotentElem (Ideal.Quotient.mk J e) := by
    rw [IsIdempotentElem, ← map_mul, ← sub_eq_zero, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact he
  obtain ⟨y, hy, hyf⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f hker
    (Ideal.Quotient.mk J e) ⟨Ideal.Quotient.mk I e, hf e⟩ hidem
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨x, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]
    exact hy.eq
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, ← hf]
    exact hyf

theorem sub_mem_span_of_mul_self_sub_mem {P : Type*} [CommRing P] [Algebra R P]
    {b : R} (hnil : ∀ c ∈ maximalIdeal R, ∃ n : ℕ, b ∣ c ^ n)
    {y y' : P} (hy : y * y - y ∈ Ideal.span {algebraMap R P b})
    (hy' : y' * y' - y' ∈ Ideal.span {algebraMap R P b})
    (hyy' : y - y' ∈ (maximalIdeal R).map (algebraMap R P)) :
    y - y' ∈ Ideal.span {algebraMap R P b} := by
  set I : Ideal P := Ideal.span {algebraMap R P b} with hI
  have h1 : IsIdempotentElem (Ideal.Quotient.mk I y) := by
    rw [IsIdempotentElem, ← map_mul, ← sub_eq_zero, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hy
  have h2 : IsIdempotentElem (Ideal.Quotient.mk I y') := by
    rw [IsIdempotentElem, ← map_mul, ← sub_eq_zero, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hy'
  have h3 : IsNilpotent (Ideal.Quotient.mk I y - Ideal.Quotient.mk I y') := by
    rw [← map_sub]
    exact isNilpotent_mk_of_mem_map hnil hyy'
  have := eq_of_isNilpotent_sub_of_isIdempotentElem h1 h2 h3
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact this

end dimOne

theorem map_mul_self_sub_mem_span {P P'' : Type*} [CommRing P] [CommRing P'']
    [Algebra R P] [Algebra R P''] (u : P →ₐ[R] P'') {b : R} {x : P}
    (hx : x * x - x ∈ Ideal.span {algebraMap R P b}) :
    u x * u x - u x ∈ Ideal.span {algebraMap R P'' b} := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_singleton']
  refine ⟨u c, ?_⟩
  have := congrArg u hc
  simpa [map_mul, map_sub, AlgHom.commutes] using this

theorem map_mem_map_maximalIdeal [IsLocalRing R] {P P'' : Type*} [CommRing P] [CommRing P'']
    [Algebra R P] [Algebra R P''] (u : P →ₐ[R] P'') {x : P}
    (hx : x ∈ (maximalIdeal R).map (algebraMap R P)) :
    u x ∈ (maximalIdeal R).map (algebraMap R P'') := by
  have h := Ideal.mem_map_of_mem u.toRingHom hx
  rw [Ideal.map_map, u.toRingHom_eq_coe, u.comp_algebraMap] at h
  exact h

end EngineCoreSol

open EngineCoreSol in
theorem solution
    {R : Type*} [CommRing R] [IsLocalRing R]
    {P P' P'' : Type*} [CommRing P] [CommRing P'] [CommRing P'']
    [Algebra R P] [Algebra R P'] [Algebra R P'']
    (u : P →ₐ[R] P'') (u' : P' →ₐ[R] P'')
    (h0 : ∀ (x : P) (x' : P'), u x = u' x' →
      ∃ r : R, x = algebraMap R P r ∧ x' = algebraMap R P' r)
    (a π : R) (hπ : π ∈ maximalIdeal R)
    (hnil : ∀ c ∈ maximalIdeal R, ∃ n : ℕ, a * π ∣ c ^ n)
    (htor : ∀ y : P'', (∃ (p : P) (p' : P'), (a * π) • y = u p + u' p') →
      ∃ (p : P) (p' : P'), a • y = u p + u' p')
    (e : P) (e' : P')
    (he : e * e - e ∈ (maximalIdeal R).map (algebraMap R P))
    (he' : e' * e' - e' ∈ (maximalIdeal R).map (algebraMap R P'))
    (hu : u e - u' e' ∈ (maximalIdeal R).map (algebraMap R P'')) :
    ∃ r : R, e - algebraMap R P r ∈ (maximalIdeal R).map (algebraMap R P) ∧
      e' - algebraMap R P' r ∈ (maximalIdeal R).map (algebraMap R P') := by
  set b : R := a * π with hb_def
  have hb : b ∈ maximalIdeal R := Ideal.mul_mem_left _ a hπ

  obtain ⟨x, hx, hxe⟩ := exists_mul_self_sub_mem_span_and_sub_mem hb hnil e he
  obtain ⟨x', hx', hxe'⟩ := exists_mul_self_sub_mem_span_and_sub_mem hb hnil e' he'

  have hux : u x * u x - u x ∈ Ideal.span {algebraMap R P'' b} := map_mul_self_sub_mem_span u hx
  have hux' : u' x' * u' x' - u' x' ∈ Ideal.span {algebraMap R P'' b} :=
    map_mul_self_sub_mem_span u' hx'
  have hdiff : u x - u' x' ∈ (maximalIdeal R).map (algebraMap R P'') := by
    have e1 : u x - u' x' = u (x - e) + (u e - u' e') - u' (x' - e') := by
      simp only [map_sub]; ring
    rw [e1]
    exact Ideal.sub_mem _ (Ideal.add_mem _ (map_mem_map_maximalIdeal u hxe) hu)
      (map_mem_map_maximalIdeal u' hxe')
  have hsub := sub_mem_span_of_mul_self_sub_mem hnil hux hux' hdiff
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hsub

  have hN : ∃ (p : P) (p' : P'), b • y = u p + u' p' := by
    refine ⟨x, -x', ?_⟩
    rw [map_neg, ← sub_eq_add_neg, ← hy, Algebra.smul_def, mul_comm]
  obtain ⟨p, q, hpq⟩ := htor y hN

  have hzero : u (x - π • p) = u' (x' + π • q) := by
    have hy' : u x - u' x' = (a * π) • y := by
      rw [← hy, Algebra.smul_def, mul_comm]
    have : u x - u' x' = π • (u p + u' q) := by
      rw [hy', ← hpq, smul_smul, mul_comm]
    rw [map_sub, map_add, map_smul, map_smul, sub_eq_iff_eq_add]
    rw [sub_eq_iff_eq_add] at this
    rw [this, smul_add]
    abel
  obtain ⟨r, hr, hr'⟩ := h0 _ _ hzero
  refine ⟨r, ?_, ?_⟩
  · have e2 : e - algebraMap R P r = π • p - (x - e) := by
      rw [← hr]; abel
    rw [e2]
    refine Ideal.sub_mem _ ?_ hxe
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπ)
  · have e3 : e' - algebraMap R P' r = -(π • q) - (x' - e') := by
      rw [← hr']; abel
    rw [e3]
    refine Ideal.sub_mem _ ((Submodule.neg_mem_iff _).mpr ?_) hxe'
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπ)

end S_IsLocalRing_exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add
end P2MW
export P2MW.S_IsLocalRing_exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add (solution)
