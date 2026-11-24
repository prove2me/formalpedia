-- Prove2me | solution 1 for GlobalTheory.CNorm.pows_eq_range_dif_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:02.195304+00:00
-- url     : https://prove2.me/submissions/cdcb3e3f-6842-4ff1-b976-7514cfe35a56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifference
import Theorems.Thm_GlobalTheory_CNorm_nrm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
namespace GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private lemma pow_apply_ofMul_eq_iterate {M : Type} [CommGroup M] (ψ : AddMonoid.End (Additive M))
    (φ : M →* M) (hψ : ∀ a, ψ (Additive.ofMul a) = Additive.ofMul (φ a)) (n : ℕ) (a : M) :
    (ψ ^ n) (Additive.ofMul a) = Additive.ofMul ((⇑φ)^[n] a) := by
  rw [AddMonoid.End.coe_pow]
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hψ]
open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private lemma cyclotomic_comp_X_add_one_eq (p : ℕ) [Fact p.Prime] :
    ∃ H : ℤ[X], (cyclotomic p ℤ).comp (X + 1) = X ^ (p - 1) + (p : ℤ[X]) * (1 + X * H) := by
  have hp : p.Prime := Fact.out
  have hE := cyclotomic_comp_X_add_one_isEisensteinAt p
  have hm : ((cyclotomic p ℤ).comp (X + 1)).Monic := (cyclotomic.monic p ℤ).comp_X_add_C 1
  have hd : ((cyclotomic p ℤ).comp (X + 1)).natDegree = p - 1 := by
    rw [natDegree_comp, natDegree_cyclotomic, Nat.totient_prime hp, ← C_1, natDegree_X_add_C, mul_one]
  obtain ⟨G, hG⟩ : C (p : ℤ) ∣ (cyclotomic p ℤ).comp (X + 1) - X ^ (p - 1) := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_X_pow]
    rcases lt_trichotomy i (p - 1) with h | h | h
    · rw [if_neg h.ne, sub_zero]
      exact Ideal.mem_span_singleton.1 (hE.mem (by rwa [hd]))
    · rw [if_pos h, h, ← hd, hm.coeff_natDegree, sub_self]
      exact dvd_zero _
    · rw [if_neg h.ne', sub_zero, coeff_eq_zero_of_natDegree_lt (by rwa [hd])]
      exact dvd_zero _
  have h0 : G.coeff 0 = 1 := by
    have h : ((cyclotomic p ℤ).comp (X + 1) - X ^ (p - 1)).coeff 0 = (C (p : ℤ) * G).coeff 0 := by
      rw [hG]
    have hp1 : (0 : ℕ) ≠ p - 1 := (Nat.sub_pos_of_lt hp.one_lt).ne
    rw [coeff_sub, coeff_X_pow, if_neg hp1, sub_zero, coeff_C_mul, coeff_zero_eq_eval_zero,
      eval_comp] at h
    simp only [eval_add, eval_X, eval_one, zero_add, eval_one_cyclotomic_prime] at h
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (mul_right_eq_self₀.1 h.symm).resolve_right hpz
  obtain ⟨H, hH⟩ : X ∣ G - 1 := by
    rw [X_dvd_iff, coeff_sub, coeff_one_zero, h0, sub_self]
  refine ⟨H, ?_⟩
  rw [← hH, ← C_eq_natCast]
  linear_combination hG
open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
private lemma exists_pow_factor_of_aeval_cyclotomic {S : Type*} [Ring S] (p : ℕ) [Fact p.Prime]
    (y : S) (hy : aeval y ((cyclotomic p ℤ).comp (X + 1)) = 0) :
    ∃ W V : S, y ^ (p - 1) = (p : S) * W ∧ y ^ (p - 1) = W * p ∧
      (p : S) = y ^ (p - 1) * V ∧ (p : S) = V * y ^ (p - 1) := by
  obtain ⟨H, hf⟩ := cyclotomic_comp_X_add_one_eq p
  have hg := mul_neg_geom_sum (-(X * H)) (p - 1)
  have h2 : (-(X * H)) ^ (p - 1) = X ^ (p - 1) * (-H) ^ (p - 1) := by rw [← mul_pow, mul_neg]
  have e1 : X ^ (p - 1) = (p : ℤ[X]) * (-(1 + X * H)) + (cyclotomic p ℤ).comp (X + 1) := by
    linear_combination -hf
  have e2 : X ^ (p - 1) = (-(1 + X * H)) * (p : ℤ[X]) + (cyclotomic p ℤ).comp (X + 1) := by
    linear_combination -hf
  have e3 : (p : ℤ[X]) = X ^ (p - 1) * ((p : ℤ[X]) * (-H) ^ (p - 1) -
      ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i) +
      (cyclotomic p ℤ).comp (X + 1) * ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i := by
    linear_combination (-(∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i)) * hf +
      (-(p : ℤ[X])) * hg + (p : ℤ[X]) * h2
  have e4 : (p : ℤ[X]) = ((p : ℤ[X]) * (-H) ^ (p - 1) -
      ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i) * X ^ (p - 1) +
      (∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i) * (cyclotomic p ℤ).comp (X + 1) := by
    linear_combination e3
  refine ⟨aeval (R := ℤ) y (-(1 + X * H) : ℤ[X]),
    aeval (R := ℤ) y ((p : ℤ[X]) * (-H) ^ (p - 1) - ∑ i ∈ Finset.range (p - 1), (-(X * H)) ^ i),
    ?_, ?_, ?_, ?_⟩
  · have h := congrArg (aeval y) e1
    rwa [map_add, map_mul, map_natCast, hy, add_zero, map_pow, aeval_X] at h
  · have h := congrArg (aeval y) e2
    rwa [map_add, map_mul, map_natCast, hy, add_zero, map_pow, aeval_X] at h
  · have h := congrArg (aeval y) e3
    rwa [map_add, map_mul, map_mul, map_natCast, hy, zero_mul, add_zero, map_pow, aeval_X] at h
  · have h := congrArg (aeval y) e4
    rwa [map_add, map_mul, map_mul, map_natCast, hy, mul_zero, add_zero, map_pow, aeval_X] at h
end GlobalTheory.CNorm
end

set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped WithZero TensorProduct
namespace GlobalTheory.CNorm
namespace _root_.GlobalTheory.CNorm
theorem _root_.solution : ∀ (p : ℕ) (M : Type) [CommGroup M] (τ : M →* M)
    (lam : Monoid.End M), p.Prime → (∀ a, lam a = τ a / a) →
    (∀ a, _root_.GlobalTheory.CNorm.nrm τ p a = 1) →
    _root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup M) = MonoidHom.range (lam ^ (p - 1) : Monoid.End M) ∧
      ∀ a : M, a ^ p = 1 ↔ (lam ^ (p - 1) : Monoid.End M) a = 1 := by
  intro p M _ τ lam hp hlam hN
  haveI : Fact p.Prime := ⟨hp⟩
  let T : AddMonoid.End (Additive M) := MonoidHom.toAdditive τ
  let Y : AddMonoid.End (Additive M) := MonoidHom.toAdditive (lam : M →* M)
  have hYT : Y + 1 = T := by
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨a, rfl⟩ : ∃ a, Additive.ofMul a = x := ⟨_, ofMul_toMul x⟩
    show Additive.ofMul (lam a) + Additive.ofMul a = Additive.ofMul (τ a)
    rw [hlam, ← ofMul_mul, div_mul_cancel]
  have hT : aeval T (cyclotomic p ℤ) = 0 := by
    rw [cyclotomic_prime, map_sum]
    simp only [map_pow, aeval_X]
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨a, rfl⟩ : ∃ a, Additive.ofMul a = x := ⟨_, ofMul_toMul x⟩
    have hs := map_sum (AddMonoidHom.mk' (fun g : AddMonoid.End (Additive M) =>
      g (Additive.ofMul a)) (fun _ _ => rfl)) (fun i => T ^ i) (Finset.range p)
    change (∑ i ∈ Finset.range p, T ^ i) (Additive.ofMul a) =
      ∑ i ∈ Finset.range p, (T ^ i) (Additive.ofMul a) at hs
    rw [hs, Finset.sum_congr rfl fun i _ => pow_apply_ofMul_eq_iterate T τ (fun _ => rfl) i a]
    rw [← ofMul_prod, ← _root_.GlobalTheory.CNorm.nrm_apply, hN, ofMul_one]
    rfl
  have hy : aeval Y ((cyclotomic p ℤ).comp (X + 1)) = 0 := by
    rw [aeval_comp, map_add, aeval_X, map_one, hYT, hT]
  obtain ⟨W, V, h1, h2, h3, h4⟩ := exists_pow_factor_of_aeval_cyclotomic p Y hy
  have hL : ∀ a, Additive.ofMul ((lam ^ (p - 1) : Monoid.End M) a) =
      (Y ^ (p - 1)) (Additive.ofMul a) := fun a => by
    rw [Monoid.End.coe_pow]
    exact (pow_apply_ofMul_eq_iterate Y lam (fun _ => rfl) _ _).symm
  have hP : ∀ a : M, ((p : AddMonoid.End (Additive M))) (Additive.ofMul a) =
      Additive.ofMul (a ^ p) := fun a => by
    rw [AddMonoid.End.natCast_apply, ofMul_pow]
  have K1 : ∀ a, (lam ^ (p - 1) : Monoid.End M) a = (Additive.toMul (W (Additive.ofMul a))) ^ p :=
    fun a => by
      apply Additive.ofMul.injective
      rw [hL, h1, ofMul_pow, ofMul_toMul, ← AddMonoid.End.natCast_apply]
      rfl
  have K2 : ∀ a, (lam ^ (p - 1) : Monoid.End M) a = Additive.toMul (W (Additive.ofMul (a ^ p))) :=
    fun a => by
      apply Additive.ofMul.injective
      rw [hL, h2, ofMul_toMul, ← hP]
      rfl
  have K3 : ∀ a : M, a ^ p = (lam ^ (p - 1) : Monoid.End M) (Additive.toMul (V (Additive.ofMul a))) :=
    fun a => by
      apply Additive.ofMul.injective
      rw [hL, ofMul_toMul, ← hP, h3]
      rfl
  have K4 : ∀ a : M, a ^ p =
      Additive.toMul (V (Additive.ofMul ((lam ^ (p - 1) : Monoid.End M) a))) := fun a => by
    apply Additive.ofMul.injective
    rw [hL, ofMul_toMul, ← hP, h4]
    rfl
  refine ⟨?_, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · ext x
    simp only [_root_.GlobalTheory.CNorm.pows, Subgroup.mem_map, Subgroup.mem_top, true_and,
      powMonoidHom_apply, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (K3 y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨_, (K1 y).symm⟩
  · rw [K2, ha, ofMul_one, map_zero, toMul_zero]
  · rw [K4, ha, ofMul_one, map_zero, toMul_zero]
end _root_.GlobalTheory.CNorm
end GlobalTheory.CNorm
