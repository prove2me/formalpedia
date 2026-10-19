-- Prove2me | solution 1 for OAI.CirculantHadamard.RamifiedLocal.exists_unit_mul_uniformizer_pow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:19:53.669339+00:00
-- url     : https://prove2.me/submissions/b7f47eb5-ab4e-41b1-bb8b-b25fff5c3d2e

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.RamifiedLocal
universe uA
open Polynomial
theorem puf_aux {R : Type*} [CommRing R] [IsDomain R] (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i) :
    ∃ q : R[X], f = X ^ f.natDegree + C a * (1 + X * q) := by
  have hdvd : C a ∣ f - X ^ f.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_X_pow]
    rcases lt_trichotomy i f.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact hcoeff i h
    · subst h; rw [if_pos rfl]; have := hf.coeff_natDegree; rw [this, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
  obtain ⟨g, hg⟩ := hdvd
  have hg0 : g.coeff 0 = 1 := by
    have := congrArg (fun p => p.coeff 0) hg
    simp only [coeff_sub, coeff_X_pow, coeff_C_mul, hzero] at this
    rw [if_neg hdeg.ne] at this
    have h2 : a * (g.coeff 0 - 1) = 0 := by rw [mul_sub, ← this]; ring
    have := (mul_eq_zero.1 h2).resolve_left ha
    exact sub_eq_zero.1 this
  have hX : X ∣ g - 1 := by
    rw [X_dvd_iff, coeff_sub, hg0, coeff_one_zero, sub_self]
  obtain ⟨q, hq⟩ := hX
  refine ⟨q, ?_⟩
  rw [← hq, add_sub_cancel, ← hg, add_sub_cancel]

theorem aux_rootpow {R : Type*} {S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [IsLocalRing S]
    (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i)
    (z : S) (hz : z ∈ IsLocalRing.maximalIdeal S) (hroot : aeval z f = 0) :
    ∃ u : Sˣ, algebraMap R S a = (u : S) * z ^ f.natDegree := by
  obtain ⟨q, hq⟩ := puf_aux f a ha hf hdeg hzero hcoeff
  rw [hq] at hroot
  simp only [map_add, map_pow, aeval_X, map_mul, aeval_C, map_one] at hroot
  have hu : IsUnit (1 + z * aeval z q) := by
    by_contra hn
    have h1 : 1 + z * aeval z q ∈ IsLocalRing.maximalIdeal S := hn
    have h2 : z * aeval z q ∈ IsLocalRing.maximalIdeal S :=
      Ideal.mul_mem_right _ _ hz
    have : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
      simpa using Ideal.sub_mem _ h1 h2
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨-hu.unit⁻¹, ?_⟩
  have key : algebraMap R S a * (1 + z * aeval z q) = -z ^ f.natDegree := by
    linear_combination hroot
  calc algebraMap R S a = algebraMap R S a * (1 + z * aeval z q) * ↑hu.unit⁻¹ := by
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
    _ = _ := by rw [key]; simp; ring

theorem aux_mspan (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {p : ℕ} (hp : p.Prime) (k : ℕ)
  (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) (M : Ideal (Extension A p k)) [M.IsMaximal] :
    M = Ideal.span {uniformizer A p k} := by
  haveI : Fact p.Prime := ⟨hp⟩
  set u := uniformizer A p k with hu
  have hint : Algebra.IsIntegral A (Extension A p k) := Algebra.IsIntegral.of_finite A _
  have hcomap : M.comap (algebraMap A (Extension A p k)) = Ideal.span {(p : A)} := by
    rw [← hmax]
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hpM : (p : Extension A p k) ∈ M := by
    have : (p : A) ∈ M.comap (algebraMap A (Extension A p k)) := by
      rw [hcomap]; exact Ideal.subset_span rfl
    simpa using this
  -- p ∈ span {u}
  have hpu : (p : Extension A p k) ∈ Ideal.span {u} := by
    obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := (1 : A)) (p := cyclotomic (p ^ (k + 1)) A)
    rw [eval_one_cyclotomic_prime_pow] at hq
    have h1 := congrArg (AdjoinRoot.mk (cyclotomic (p ^ (k + 1)) A)) hq
    rw [map_sub, AdjoinRoot.mk_self, map_mul, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      AdjoinRoot.mk_C, map_one, zero_sub, map_natCast] at h1
    rw [Ideal.mem_span_singleton]
    exact ⟨-AdjoinRoot.mk _ q, by rw [hu, uniformizer]; linear_combination -h1⟩
  -- u ∈ M
  have huM : u ∈ M := by
    let Q := Extension A p k ⧸ M
    haveI : Field Q := Ideal.Quotient.field M
    haveI : CharP Q p := (CharP.charP_iff_prime_eq_zero hp).2 (by
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]; exact hpM)
    have hroot : (AdjoinRoot.root (cyclotomic (p ^ (k + 1)) A)) ^ (p ^ (k + 1)) = 1 := by
      have h : AdjoinRoot.mk (cyclotomic (p ^ (k + 1)) A) (X ^ (p ^ (k + 1)) - 1) = 0 :=
        AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one _ A)
      simpa only [map_sub, map_pow, map_one, AdjoinRoot.mk_X, sub_eq_zero] using h
    have h0 : (Ideal.Quotient.mk M u) ^ (p ^ (k + 1)) = 0 := by
      rw [hu, uniformizer, map_sub, map_one, sub_pow_char_pow, ← map_pow, hroot, map_one, one_pow,
        sub_self]
    have := pow_eq_zero_iff (n := p ^ (k + 1)) (pow_ne_zero _ hp.ne_zero) |>.1 h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := (1 : A)) (p := g)
    have hg : AdjoinRoot.mk _ g = algebraMap A (Extension A p k) (g.eval 1) + u * AdjoinRoot.mk _ q := by
      have : g = C (g.eval 1) + (X - C 1) * q := by rw [← hq]; ring
      conv_lhs => rw [this]
      simp [hu, uniformizer, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
    have ha : algebraMap A (Extension A p k) (g.eval 1) ∈ M := by
      have := M.sub_mem hx (M.mul_mem_right (AdjoinRoot.mk _ q) huM)
      rw [hg] at this; simpa using this
    have ha' : g.eval 1 ∈ Ideal.span {(p : A)} := by rw [← hcomap]; exact ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha'
    rw [hg, ← hc, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpu)
      (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · rw [Ideal.span_le, Set.singleton_subset_iff]; exact huM


variable (A : Type uA) [CommRing A] [IsDomain A] [CharZero A]
  [IsDiscreteValuationRing A] {p : ℕ} (hp : p.Prime) (k : ℕ)
  (hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
include hp hmax
variable [IsLocalRing (Extension A p k)]
theorem solution :
    ∃ u : (Extension A p k)ˣ,
      (p : Extension A p k) = (u : Extension A p k) *
        uniformizer A p k ^ ((p - 1) * p ^ k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set fZ : ℤ[X] := (cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1) with hfZ
  have hE := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k
  set f : A[X] := fZ.map (Int.castRingHom A) with hf
  have h1 : (X + 1 : ℤ[X]).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ℤ)
  have hX1 : (X + 1 : ℤ[X]).Monic := by simpa using monic_X_add_C (1 : ℤ)
  have hfZmonic : fZ.Monic := (cyclotomic.monic _ ℤ).comp hX1 (by rw [h1]; norm_num)
  have hdegZ : fZ.natDegree = (p - 1) * p ^ k := by
    rw [hfZ, natDegree_comp, natDegree_cyclotomic, h1, mul_one,
      Nat.totient_prime_pow_succ hp, mul_comm]
  have hdeg : f.natDegree = (p - 1) * p ^ k := by
    rw [hf, hfZmonic.natDegree_map, hdegZ]
  have hf0 : f.coeff 0 = (p : A) := by
    rw [hf, coeff_map, coeff_zero_eq_eval_zero, hfZ, eval_comp]
    simp [eval_one_cyclotomic_prime_pow]
  have hp0 : (p : A) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcoeff : ∀ i < f.natDegree, (p : A) ∣ f.coeff i := by
    intro i hi
    rw [hf, hfZmonic.natDegree_map] at hi
    have := hE.mem hi
    rw [Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    rw [hf, coeff_map, hc]
    exact ⟨(c : A), by simp⟩
  have hu : uniformizer A p k ∈ IsLocalRing.maximalIdeal (Extension A p k) := by
    rw [aux_mspan A hp k hmax (IsLocalRing.maximalIdeal _)]
    exact Ideal.subset_span rfl
  have hroot : aeval (uniformizer A p k) f = 0 := by
    have hmap : f = (cyclotomic (p ^ (k + 1)) A).comp (X + 1) := by
      rw [hf, hfZ, Polynomial.map_comp, map_cyclotomic]; simp
    rw [hmap, aeval_comp]
    simp only [map_add, aeval_X, map_one, uniformizer, sub_add_cancel]
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hdpos : 0 < f.natDegree := by
    rw [hdeg]; exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos k)
  obtain ⟨w, hw⟩ := aux_rootpow f (p : A) hp0 (hfZmonic.map _) hdpos hf0 hcoeff
    (uniformizer A p k) hu hroot
  refine ⟨w, ?_⟩
  rw [← hdeg, ← hw, map_natCast]
