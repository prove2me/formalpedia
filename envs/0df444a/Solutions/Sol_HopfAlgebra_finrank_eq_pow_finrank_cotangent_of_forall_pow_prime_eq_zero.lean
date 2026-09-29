-- Prove2me | solution 1 for HopfAlgebra.finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/34e1cc4a-7aa0-5649-b251-f432c383d2bf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero

set_option autoImplicit false

open scoped TensorProduct
open Finset

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk"
namespace HeightOne
p2m_open "HopfAlgebra"

universe u v

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Bialgebra k A]

local notation "ε" => Coalgebra.counit (R := k) (A := A)

abbrev augIdeal (k : Type u) [Field k] (A : Type v) [CommRing A] [Bialgebra k A] : Ideal A :=
  RingHom.ker (Bialgebra.counitAlgHom k A)

local notation "I" => augIdeal k A

theorem mem_augIdeal_iff (a : A) : a ∈ I ↔ ε a = 0 := RingHom.mem_ker

theorem sub_smul_one_mem (a : A) : a - ε a • (1 : A) ∈ I := by
  rw [mem_augIdeal_iff, map_sub, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one, sub_self]

structure IsTangent (t : A →ₗ[k] k) : Prop where
  map_one : t 1 = 0
  map_mul_mem : ∀ u ∈ I, ∀ v ∈ I, t (u * v) = 0

namespace IsTangent

variable {t : A →ₗ[k] k}

theorem map_mul (ht : IsTangent t) (u v : A) : t (u * v) = ε u * t v + ε v * t u := by
  have hu := sub_smul_one_mem (k := k) u
  have hv := sub_smul_one_mem (k := k) v
  have h := ht.map_mul_mem _ hu _ hv
  have e : (u - ε u • (1 : A)) * (v - ε v • (1 : A)) =
      u * v - ε v • u - ε u • v + (ε u * ε v) • (1 : A) := by
    rw [mul_smul]
    simp only [Algebra.smul_def, mul_one]
    ring
  rw [e, map_add, map_sub, map_sub, map_smul, map_smul, map_smul, ht.map_one, smul_zero, add_zero,
    smul_eq_mul, smul_eq_mul] at h

  linear_combination h

end IsTangent

variable (t : A →ₗ[k] k)

noncomputable def der : A →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A t ∘ₗ Coalgebra.comul

theorem der_eq_sum {a : A} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr k a ι𝓡) :
    der t a = ∑ i ∈ 𝓡.index, t (𝓡.right i) • 𝓡.left i := by
  simp only [der, LinearMap.comp_apply, ← 𝓡.eq, map_sum, LinearMap.lTensor_tmul,
    LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul]

omit [Field k] in
theorem sum_counit_right_smul_left {k : Type u} [CommRing k] [Bialgebra k A] {a : A}
    {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr k a ι𝓡) :
    ∑ i ∈ 𝓡.index, Coalgebra.counit (R := k) (𝓡.right i) • 𝓡.left i = a := by
  have h := congrArg (TensorProduct.rid k A) (Coalgebra.sum_tmul_counit_eq (R := k) 𝓡)
  simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using h

theorem counit_der (a : A) : ε (der t a) = t a := by
  let 𝓡 := Coalgebra.Repr.arbitrary k a
  rw [der_eq_sum t 𝓡, map_sum]
  simp only [map_smul, smul_eq_mul]
  have h := congrArg t (Coalgebra.sum_counit_smul (R := k) 𝓡)
  rw [map_sum] at h
  simp only [map_smul, smul_eq_mul] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

variable {t}

theorem der_mul (ht : IsTangent t) (a b : A) : der t (a * b) = a * der t b + b * der t a := by
  let 𝓐 := Coalgebra.Repr.arbitrary k a
  let 𝓑 := Coalgebra.Repr.arbitrary k b

  have hab : Coalgebra.comul (R := k) (a * b) =
      ∑ ij ∈ 𝓐.index ×ˢ 𝓑.index, (𝓐.left ij.1 * 𝓑.left ij.2) ⊗ₜ[k] (𝓐.right ij.1 * 𝓑.right ij.2) := by
    rw [Bialgebra.comul_mul, ← 𝓐.eq, ← 𝓑.eq, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul]
  let 𝓒 : Coalgebra.Repr k (a * b) _ :=
    { index := 𝓐.index ×ˢ 𝓑.index
      left := fun ij => 𝓐.left ij.1 * 𝓑.left ij.2
      right := fun ij => 𝓐.right ij.1 * 𝓑.right ij.2
      eq := hab.symm }
  rw [der_eq_sum t 𝓒]
  change ∑ ij ∈ 𝓐.index ×ˢ 𝓑.index,
      t (𝓐.right ij.1 * 𝓑.right ij.2) • (𝓐.left ij.1 * 𝓑.left ij.2) = _
  simp only [ht.map_mul, add_smul, Finset.sum_add_distrib]
  rw [Finset.sum_product, Finset.sum_product]
  have h1 : ∑ i ∈ 𝓐.index, ∑ j ∈ 𝓑.index,
      (ε (𝓐.right i) * t (𝓑.right j)) • (𝓐.left i * 𝓑.left j) =
      (∑ i ∈ 𝓐.index, ε (𝓐.right i) • 𝓐.left i) * der t b := by
    rw [der_eq_sum t 𝓑, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, mul_smul]
  have h2 : ∑ i ∈ 𝓐.index, ∑ j ∈ 𝓑.index,
      (ε (𝓑.right j) * t (𝓐.right i)) • (𝓐.left i * 𝓑.left j) =
      (∑ j ∈ 𝓑.index, ε (𝓑.right j) • 𝓑.left j) * der t a := by
    rw [der_eq_sum t 𝓐, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, mul_comm (𝓐.left j)]
  rw [h1, h2, sum_counit_right_smul_left 𝓐, sum_counit_right_smul_left 𝓑]

theorem der_one (ht : IsTangent t) : der t (1 : A) = 0 := by
  have h := der_mul ht (1 : A) 1
  simp only [mul_one, one_mul] at h

  linear_combination -h

theorem der_pow (ht : IsTangent t) (y : A) (n : ℕ) :
    der t (y ^ n) = (n : A) * y ^ (n - 1) * der t y := by
  induction n with
  | zero => rw [pow_zero, der_one ht, Nat.cast_zero, zero_mul, zero_mul]
  | succ n ih =>
    rw [pow_succ, der_mul ht, ih, Nat.cast_succ, Nat.add_sub_cancel]
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      ring

theorem der_prod (ht : IsTangent t) {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    der t (∏ j ∈ s, f j) = ∑ j ∈ s, (∏ l ∈ s.erase j, f l) * der t (f j) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, der_one ht]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, der_mul ht, ih, Finset.sum_insert hi, Finset.erase_insert hi,
      add_comm, Finset.mul_sum s _ (f i)]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Finset.erase_insert_of_ne hij, Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h)),
      mul_assoc]

theorem der_sub_smul_one_mem (a : A) : der t a - t a • (1 : A) ∈ I := by
  have := sub_smul_one_mem (k := k) (der t a)
  rwa [counit_der] at this

theorem der_mem_pow (ht : IsTangent t) :
    ∀ (m : ℕ) {a : A}, a ∈ I ^ (m + 1) → der t a ∈ I ^ m := by
  intro m
  induction m with
  | zero => intro a _; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ m ih =>
    intro a ha
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha (fun u hu v hv => ?_) (fun x y hx hy => ?_)
    · rw [der_mul ht]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hu (ih hv)
      · exact Ideal.mul_mem_right _ _ hv
    · rw [map_add]; exact Ideal.add_mem _ hx hy

section System

variable {r : ℕ} (x : Fin r → A) (τ : Fin r → (A →ₗ[k] k))

structure IsSystem : Prop where
  mem : ∀ i, x i ∈ I
  tangent : ∀ i, IsTangent (τ i)
  dual : ∀ i j, τ i (x j) = if i = j then 1 else 0

variable {x τ}

noncomputable def mono (x : Fin r → A) (ν : Fin r → ℕ) : A := ∏ j, x j ^ ν j

def deg (ν : Fin r → ℕ) : ℕ := ∑ j, ν j

theorem prod_pow_mem_pow (hx : ∀ i, x i ∈ I) (s : Finset (Fin r)) (ν : Fin r → ℕ) :
    ∏ j ∈ s, x j ^ ν j ∈ I ^ (∑ j ∈ s, ν j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hx i) _) ih

theorem mono_mem_pow (hx : ∀ i, x i ∈ I) (ν : Fin r → ℕ) : mono x ν ∈ I ^ deg ν :=
  prod_pow_mem_pow hx _ ν

def lower (ν : Fin r → ℕ) (i : Fin r) : Fin r → ℕ := Function.update ν i (ν i - 1)

theorem lower_apply (ν : Fin r → ℕ) (i j : Fin r) :
    lower ν i j = if j = i then ν i - 1 else ν j := by
  unfold lower
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem der_mono_sub_mem (h : IsSystem x τ) (ν : Fin r → ℕ) (i : Fin r) :
    der (τ i) (mono x ν) - (ν i : A) * mono x (lower ν i) ∈ I ^ deg ν := by
  classical
  have hprod := der_prod (h.tangent i) (Finset.univ : Finset (Fin r)) (fun j => x j ^ ν j)
  rw [show mono x ν = ∏ j, x j ^ ν j from rfl, hprod]

  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i, (∏ l ∈ (Finset.univ.erase j), x l ^ ν l) *
      der (τ i) (x j ^ ν j) ∈ I ^ deg ν := by
    refine Ideal.sum_mem _ fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [der_pow (h.tangent i)]

    have hd : der (τ i) (x j) ∈ I := by
      have := der_sub_smul_one_mem (t := τ i) (x j)
      rwa [h.dual i j, if_neg hji.symm, zero_smul, sub_zero] at this
    rcases Nat.eq_zero_or_pos (ν j) with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_mul, zero_mul, mul_zero]; exact Ideal.zero_mem _
    · have hmem : (∏ l ∈ Finset.univ.erase j, x l ^ ν l) * x j ^ (ν j - 1) * der (τ i) (x j) ∈
          I ^ ((∑ l ∈ Finset.univ.erase j, ν l) + (ν j - 1) + 1) := by
        rw [pow_add, pow_add, pow_one]
        exact Ideal.mul_mem_mul (Ideal.mul_mem_mul (prod_pow_mem_pow h.mem _ ν)
          (Ideal.pow_mem_pow (h.mem j) _)) hd
      have hdeg : (∑ l ∈ Finset.univ.erase j, ν l) + (ν j - 1) + 1 = deg ν := by
        unfold deg
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        omega
      rw [hdeg] at hmem
      have e : (∏ l ∈ Finset.univ.erase j, x l ^ ν l) * ((ν j : A) * x j ^ (ν j - 1) * der (τ i) (x j)) =
          (ν j : A) * ((∏ l ∈ Finset.univ.erase j, x l ^ ν l) * x j ^ (ν j - 1) * der (τ i) (x j)) := by
        ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hmem

  have hmain : (∏ l ∈ Finset.univ.erase i, x l ^ ν l) * der (τ i) (x i ^ ν i) -
      (ν i : A) * mono x (lower ν i) ∈ I ^ deg ν := by
    rw [der_pow (h.tangent i)]

    have hd : der (τ i) (x i) - 1 ∈ I := by
      have := der_sub_smul_one_mem (t := τ i) (x i)
      rwa [h.dual i i, if_pos rfl, one_smul] at this
    have hlow : mono x (lower ν i) = (∏ l ∈ Finset.univ.erase i, x l ^ ν l) * x i ^ (ν i - 1) := by
      unfold mono
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      congr 1
      · refine Finset.prod_congr rfl fun l hl => ?_
        rw [lower_apply, if_neg (Finset.ne_of_mem_erase hl)]
      · rw [lower_apply, if_pos rfl]
    rcases Nat.eq_zero_or_pos (ν i) with h0 | hpos
    · rw [h0, Nat.cast_zero, zero_mul, zero_mul, mul_zero, zero_mul, sub_zero]
      exact Ideal.zero_mem _
    · have e : (∏ l ∈ Finset.univ.erase i, x l ^ ν l) * ((ν i : A) * x i ^ (ν i - 1) * der (τ i) (x i)) -
          (ν i : A) * mono x (lower ν i) =
          (ν i : A) * ((∏ l ∈ Finset.univ.erase i, x l ^ ν l) * x i ^ (ν i - 1) *
            (der (τ i) (x i) - 1)) := by
        rw [hlow]; ring
      rw [e]
      refine Ideal.mul_mem_left _ _ ?_
      have hmem : (∏ l ∈ Finset.univ.erase i, x l ^ ν l) * x i ^ (ν i - 1) * (der (τ i) (x i) - 1) ∈
          I ^ ((∑ l ∈ Finset.univ.erase i, ν l) + (ν i - 1) + 1) := by
        rw [pow_add, pow_add, pow_one]
        exact Ideal.mul_mem_mul (Ideal.mul_mem_mul (prod_pow_mem_pow h.mem _ ν)
          (Ideal.pow_mem_pow (h.mem i) _)) hd
      have hdeg : (∑ l ∈ Finset.univ.erase i, ν l) + (ν i - 1) + 1 = deg ν := by
        unfold deg
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        omega
      rwa [hdeg] at hmem
  have e : (∏ l ∈ Finset.univ.erase i, x l ^ ν l) * der (τ i) (x i ^ ν i) +
      ∑ j ∈ Finset.univ.erase i, (∏ l ∈ Finset.univ.erase j, x l ^ ν l) * der (τ i) (x j ^ ν j) -
      (ν i : A) * mono x (lower ν i) =
      ((∏ l ∈ Finset.univ.erase i, x l ^ ν l) * der (τ i) (x i ^ ν i) -
        (ν i : A) * mono x (lower ν i)) +
      ∑ j ∈ Finset.univ.erase i, (∏ l ∈ Finset.univ.erase j, x l ^ ν l) * der (τ i) (x j ^ ν j) := by
    ring
  rw [e]
  exact Ideal.add_mem _ hmain hrest

theorem mono_eq_mul_lower (ν : Fin r → ℕ) (i : Fin r) (hi : ν i ≠ 0) :
    mono x ν = x i * mono x (lower ν i) := by
  unfold mono
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have h1 : ∏ l ∈ Finset.univ.erase i, x l ^ lower ν i l = ∏ l ∈ Finset.univ.erase i, x l ^ ν l :=
    Finset.prod_congr rfl fun l hl => by rw [lower_apply, if_neg (Finset.ne_of_mem_erase hl)]
  rw [h1, lower_apply, if_pos rfl]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [hm, Nat.succ_sub_one, pow_succ]
  ring

def nat {p : ℕ} (ν : Fin r → Fin p) : Fin r → ℕ := fun j => (ν j : ℕ)

@[scoped simp] theorem nat_apply {p : ℕ} (ν : Fin r → Fin p) (j : Fin r) : nat ν j = (ν j : ℕ) := rfl

variable {p : ℕ}

def lowerF (ν : Fin r → Fin p) (i : Fin r) : Fin r → Fin p :=
  Function.update ν i ⟨(ν i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) (ν i).2⟩

def raiseF (μ : Fin r → Fin p) (i : Fin r) (h : (μ i : ℕ) + 1 < p) : Fin r → Fin p :=
  Function.update μ i ⟨(μ i : ℕ) + 1, h⟩

theorem lowerF_apply (ν : Fin r → Fin p) (i j : Fin r) :
    (lowerF ν i j : ℕ) = if j = i then (ν i : ℕ) - 1 else (ν j : ℕ) := by
  unfold lowerF
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem raiseF_apply (μ : Fin r → Fin p) (i j : Fin r) (h : (μ i : ℕ) + 1 < p) :
    (raiseF μ i h j : ℕ) = if j = i then (μ i : ℕ) + 1 else (μ j : ℕ) := by
  unfold raiseF
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

theorem nat_lowerF (ν : Fin r → Fin p) (i : Fin r) : nat (lowerF ν i) = lower (nat ν) i := by
  funext j
  rw [nat_apply, lowerF_apply, lower_apply, nat_apply, nat_apply]

theorem lower_nat_raiseF (μ : Fin r → Fin p) (i : Fin r) (h : (μ i : ℕ) + 1 < p) :
    lower (nat (raiseF μ i h)) i = nat μ := by
  funext j
  rw [lower_apply, nat_apply, nat_apply, raiseF_apply, if_pos rfl, nat_apply]
  by_cases hj : j = i
  · subst hj; simp
  · rw [if_neg hj, raiseF_apply, if_neg hj]

theorem raiseF_lowerF (ν : Fin r → Fin p) (i : Fin r) (hi : (ν i : ℕ) ≠ 0)
    (h : (lowerF ν i i : ℕ) + 1 < p) : raiseF (lowerF ν i) i h = ν := by
  funext j
  apply Fin.ext
  rw [raiseF_apply, lowerF_apply, if_pos rfl]
  by_cases hj : j = i
  · subst hj; rw [if_pos rfl]; omega
  · rw [if_neg hj, lowerF_apply, if_neg hj]

theorem lowerF_raiseF (μ : Fin r → Fin p) (i : Fin r) (h : (μ i : ℕ) + 1 < p) :
    lowerF (raiseF μ i h) i = μ := by
  funext j
  apply Fin.ext
  rw [lowerF_apply, raiseF_apply, if_pos rfl]
  by_cases hj : j = i
  · subst hj; rw [if_pos rfl]; omega
  · rw [if_neg hj, raiseF_apply, if_neg hj]

theorem deg_nat_lowerF (ν : Fin r → Fin p) (i : Fin r) (hi : (ν i : ℕ) ≠ 0) :
    deg (nat (lowerF ν i)) + 1 = deg (nat ν) := by
  unfold deg
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : ∑ l ∈ Finset.univ.erase i, nat (lowerF ν i) l = ∑ l ∈ Finset.univ.erase i, nat ν l :=
    Finset.sum_congr rfl fun l hl => by
      rw [nat_apply, lowerF_apply, if_neg (Finset.ne_of_mem_erase hl), nat_apply]
  rw [h1, nat_apply, lowerF_apply, if_pos rfl, nat_apply]
  omega

theorem exists_ne_zero_of_deg_ne_zero (ν : Fin r → Fin p) (h : deg (nat ν) ≠ 0) :
    ∃ i, (ν i : ℕ) ≠ 0 := by
  by_contra hne
  push Not at hne
  apply h
  unfold deg
  exact Finset.sum_eq_zero fun j _ => hne j

theorem eq_of_deg_eq_zero (ν μ : Fin r → Fin p) (hν : deg (nat ν) = 0) (hμ : deg (nat μ) = 0) : ν = μ := by
  unfold deg at hν hμ
  rw [Finset.sum_eq_zero_iff] at hν hμ
  funext j
  exact Fin.ext ((hν j (Finset.mem_univ j)).trans (hμ j (Finset.mem_univ j)).symm)

def Q (x : Fin r → A) (p : ℕ) (d : ℕ) : Prop :=
  ∀ c : (Fin r → Fin p) → k,
    (∑ ν ∈ Finset.univ.filter (fun ν => deg (nat ν) = d), c ν • mono x (nat ν)) ∈ I ^ (d + 1) →
    ∀ ν : Fin r → Fin p, deg (nat ν) = d → c ν = 0

theorem Q_zero : Q (k := k) (A := A) x p 0 := by
  intro c hc ν hν

  have hfilter : Finset.univ.filter (fun μ : Fin r → Fin p => deg (nat μ) = 0) = {ν} := by
    ext μ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hμ => eq_of_deg_eq_zero μ ν hμ hν, fun hμ => hμ ▸ hν⟩
  rw [hfilter, Finset.sum_singleton, pow_one] at hc
  have hmono : mono x (nat ν) = 1 := by
    unfold mono
    refine Finset.prod_eq_one fun j _ => ?_
    unfold deg at hν
    rw [Finset.sum_eq_zero_iff] at hν
    rw [hν j (Finset.mem_univ j), pow_zero]
  rw [hmono, mem_augIdeal_iff, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one] at hc
  exact hc

theorem Q_succ [CharP k p] (h : IsSystem x τ) (d : ℕ) (IH : Q (k := k) x p d) : Q (k := k) x p (d + 1) := by
  classical
  intro c hc ν hν
  obtain ⟨i, hi⟩ := exists_ne_zero_of_deg_ne_zero ν (by omega)

  set S := ∑ ν ∈ Finset.univ.filter (fun ν : Fin r → Fin p => deg (nat ν) = d + 1),
    c ν • mono x (nat ν) with hS
  have hDS : der (τ i) S ∈ I ^ (d + 1) := der_mem_pow (h.tangent i) (d + 1) hc

  set T := ∑ ν ∈ Finset.univ.filter (fun ν : Fin r → Fin p => deg (nat ν) = d + 1),
    (c ν * ((ν i : ℕ) : k)) • mono x (lower (nat ν) i) with hT
  have hT_mem : T ∈ I ^ (d + 1) := by
    have hdiff : der (τ i) S - T ∈ I ^ (d + 1) := by
      rw [hS, hT, map_sum, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun μ hμ => ?_
      rw [Finset.mem_filter] at hμ
      rw [map_smul, mul_smul, ← smul_sub]
      refine Submodule.smul_of_tower_mem _ (c μ) ?_
      have key := der_mono_sub_mem h (nat μ) i
      rw [hμ.2, nat_apply] at key
      have e : ((μ i : ℕ) : k) • mono x (lower (nat μ) i) = ((μ i : ℕ) : A) * mono x (lower (nat μ) i) := by
        rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      rw [e]
      exact key
    have := Ideal.sub_mem _ hDS hdiff
    rwa [sub_sub_cancel] at this

  let c' : (Fin r → Fin p) → k := fun μ =>
    if hμ : (μ i : ℕ) + 1 < p then c (raiseF μ i hμ) * (((μ i : ℕ) + 1 : ℕ) : k) else 0
  have hT_eq : T = ∑ μ ∈ Finset.univ.filter (fun μ : Fin r → Fin p => deg (nat μ) = d),
      c' μ • mono x (nat μ) := by

    have hL : T = ∑ ν ∈ Finset.univ.filter
        (fun ν : Fin r → Fin p => deg (nat ν) = d + 1 ∧ (ν i : ℕ) ≠ 0),
        (c ν * ((ν i : ℕ) : k)) • mono x (lower (nat ν) i) := by
      rw [hT]
      symm
      refine Finset.sum_subset (fun ν hν => ?_) (fun ν hν hν' => ?_)
      · rw [Finset.mem_filter] at hν ⊢; exact ⟨hν.1, hν.2.1⟩
      · rw [Finset.mem_filter] at hν hν'
        have h0 : (ν i : ℕ) = 0 := by
          by_contra h0; exact hν' ⟨hν.1, hν.2, h0⟩
        rw [h0, Nat.cast_zero, mul_zero, zero_smul]
    have hR : ∑ μ ∈ Finset.univ.filter (fun μ : Fin r → Fin p => deg (nat μ) = d),
        c' μ • mono x (nat μ) =
        ∑ μ ∈ Finset.univ.filter (fun μ : Fin r → Fin p => deg (nat μ) = d ∧ (μ i : ℕ) + 1 < p),
        c' μ • mono x (nat μ) := by
      symm
      refine Finset.sum_subset (fun μ hμ => ?_) (fun μ hμ hμ' => ?_)
      · rw [Finset.mem_filter] at hμ ⊢; exact ⟨hμ.1, hμ.2.1⟩
      · rw [Finset.mem_filter] at hμ hμ'
        have h0 : ¬ ((μ i : ℕ) + 1 < p) := fun h0 => hμ' ⟨hμ.1, hμ.2, h0⟩
        simp only [c', dif_neg h0, zero_smul]
    rw [hL, hR]
    refine Finset.sum_bij' (fun ν _ => lowerF ν i) (fun μ hμ => raiseF μ i (Finset.mem_filter.1 hμ).2.2)
      (fun ν hν => ?_) (fun μ hμ => ?_) (fun ν hν => ?_) (fun μ hμ => ?_) (fun ν hν => ?_)
    · rw [Finset.mem_filter] at hν ⊢
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have := deg_nat_lowerF ν i hν.2.2; omega
      · rw [lowerF_apply, if_pos rfl]; have := (ν i).2; omega
    · rw [Finset.mem_filter] at hμ ⊢
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have h1 := deg_nat_lowerF (raiseF μ i hμ.2.2) i (by rw [raiseF_apply, if_pos rfl]; omega)
        rw [lowerF_raiseF] at h1
        omega
      · rw [raiseF_apply, if_pos rfl]; omega
    · exact raiseF_lowerF ν i (Finset.mem_filter.1 hν).2.2 _
    · exact lowerF_raiseF μ i _
    · rw [Finset.mem_filter] at hν
      have hlt : ((lowerF ν i) i : ℕ) + 1 < p := by
        rw [lowerF_apply, if_pos rfl]; have := (ν i).2; omega
      simp only [c', dif_pos hlt]
      rw [raiseF_lowerF ν i hν.2.2, nat_lowerF, lowerF_apply, if_pos rfl]
      congr 2
      have := hν.2.2
      push_cast
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
  rw [hT_eq] at hT_mem

  have hμdeg : deg (nat (lowerF ν i)) = d := by have := deg_nat_lowerF ν i hi; omega
  have hc' := IH c' hT_mem (lowerF ν i) hμdeg
  have hlt : ((lowerF ν i) i : ℕ) + 1 < p := by
    rw [lowerF_apply, if_pos rfl]; have := (ν i).2; omega
  simp only [c', dif_pos hlt, raiseF_lowerF ν i hi] at hc'

  have hunit : ((((lowerF ν i) i : ℕ) + 1 : ℕ) : k) ≠ 0 := by
    rw [lowerF_apply, if_pos rfl]
    intro h0
    rw [CharP.cast_eq_zero_iff k p] at h0
    have h1 := Nat.le_of_dvd (by omega) h0
    have h2 := (ν i).2
    omega
  exact (mul_eq_zero.1 hc').resolve_right hunit

theorem Q_all [CharP k p] (h : IsSystem x τ) (d : ℕ) : Q (k := k) x p d := by
  induction d with
  | zero => exact Q_zero
  | succ d ih => exact Q_succ h d ih

theorem linearIndependent_mono [CharP k p] (h : IsSystem x τ) :
    LinearIndependent k (fun ν : Fin r → Fin p => mono x (nat ν)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg

  suffices H : ∀ d, ∀ ν : Fin r → Fin p, deg (nat ν) = d → g ν = 0 from fun ν => H _ ν rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro ν hν
    refine Q_all h d g ?_ ν hν

    have hsplit : ∑ μ ∈ Finset.univ.filter (fun μ : Fin r → Fin p => deg (nat μ) = d),
        g μ • mono x (nat μ) =
        - ∑ μ ∈ Finset.univ.filter (fun μ : Fin r → Fin p => d < deg (nat μ)), g μ • mono x (nat μ) := by
      rw [eq_neg_iff_add_eq_zero]
      have hg' := hg
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun μ : Fin r → Fin p => deg (nat μ) = d)] at hg'
      rw [← hg']
      congr 1

      refine Finset.sum_subset (fun μ hμ => ?_) (fun μ hμ hμ' => ?_)
      · rw [Finset.mem_filter] at hμ ⊢; exact ⟨hμ.1, ne_of_gt hμ.2⟩
      · rw [Finset.mem_filter] at hμ hμ'
        have hlt : deg (nat μ) < d := by
          rcases Nat.lt_trichotomy (deg (nat μ)) d with h1 | h1 | h1
          · exact h1
          · exact absurd h1 hμ.2
          · exact absurd ⟨hμ.1, h1⟩ hμ'
        rw [ih _ hlt μ rfl, zero_smul]
    rw [hsplit]
    refine Submodule.neg_mem _ (Ideal.sum_mem _ fun μ hμ => ?_)
    rw [Finset.mem_filter] at hμ
    refine Submodule.smul_of_tower_mem _ (g μ) ?_
    exact Ideal.pow_le_pow_right hμ.2 (mono_mem_pow h.mem (nat μ))

noncomputable def W (x : Fin r → A) (p : ℕ) : Submodule k A :=
  Submodule.span k (Set.range fun ν : Fin r → Fin p => mono x (nat ν))

theorem mono_mem_W (ν : Fin r → Fin p) : mono x (nat ν) ∈ W (k := k) x p :=
  Submodule.subset_span ⟨ν, rfl⟩

theorem mul_mem_W (hxp : ∀ i, x i ^ p = 0) (i : Fin r) {w : A} (hw : w ∈ W (k := k) x p) :
    x i * w ∈ W (k := k) x p := by
  induction hw using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨μ, rfl⟩ := ha
    by_cases hμ : (μ i : ℕ) + 1 < p
    ·
      have e : x i * mono x (nat μ) = mono x (nat (raiseF μ i hμ)) := by
        rw [mono_eq_mul_lower (x := x) (nat (raiseF μ i hμ)) i
          (by rw [nat_apply, raiseF_apply, if_pos rfl]; omega), lower_nat_raiseF]
      rw [e]; exact mono_mem_W _
    ·
      have hp' : (μ i : ℕ) + 1 = p := by have := (μ i).2; omega
      have e : x i * mono x (nat μ) = 0 := by
        unfold mono
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), nat_apply, mul_comm, mul_assoc,
          ← pow_succ, hp', hxp i, mul_zero]
      rw [e]; exact Submodule.zero_mem _
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha

theorem one_mem_W [NeZero p] : (1 : A) ∈ W (k := k) x p := by
  have e : mono x (nat (fun _ : Fin r => (0 : Fin p))) = 1 := by
    unfold mono
    exact Finset.prod_eq_one fun j _ => by rw [nat_apply, Fin.val_zero, pow_zero]
  rw [← e]; exact mono_mem_W _

theorem pow_le_W_sup [NeZero p] (hxp : ∀ i, x i ^ p = 0)
    (hgen : ∀ u ∈ I, ∃ c : Fin r → k, u - ∑ i, c i • x i ∈ I ^ 2) :
    ∀ (m : ℕ) {a : A}, a ∈ I ^ m → a ∈ W (k := k) x p ⊔ (I ^ (m + 1)).restrictScalars k := by
  intro m
  induction m with
  | zero =>
    intro a _
    rw [Submodule.mem_sup]
    refine ⟨ε a • (1 : A), Submodule.smul_mem _ _ one_mem_W, a - ε a • (1 : A), ?_, by abel⟩
    rw [Submodule.restrictScalars_mem, zero_add, pow_one]
    exact sub_smul_one_mem a
  | succ m ih =>
    intro a ha
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha (fun u hu v hv => ?_) (fun y z hy hz => Submodule.add_mem _ hy hz)
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 (ih hv)
    rw [Submodule.restrictScalars_mem] at hz
    have hwI : w ∈ I ^ m := by
      have : w + z - z ∈ I ^ m := Ideal.sub_mem _ hv (Ideal.pow_le_pow_right (Nat.le_succ m) hz)
      rwa [add_sub_cancel_right] at this
    obtain ⟨c, hc⟩ := hgen u hu

    have e : u * (w + z) = ∑ i, c i • (x i * w) + ((u - ∑ i, c i • x i) * w + u * z) := by
      rw [Finset.sum_congr rfl fun i _ => (smul_mul_assoc (c i) (x i) w).symm, ← Finset.sum_mul]
      ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (mul_mem_W hxp i hw))) (Submodule.mem_sup_right ?_)
    rw [Submodule.restrictScalars_mem]
    refine Ideal.add_mem _ ?_ ?_
    · have : (u - ∑ i, c i • x i) * w ∈ I ^ 2 * I ^ m := Ideal.mul_mem_mul hc hwI
      rw [← pow_add] at this
      rw [show m + 1 + 1 = 2 + m by omega]
      exact this
    · rw [pow_succ']
      exact Ideal.mul_mem_mul hu hz

theorem W_eq_top [NeZero p] (hxp : ∀ i, x i ^ p = 0)
    (hgen : ∀ u ∈ I, ∃ c : Fin r → k, u - ∑ i, c i • x i ∈ I ^ 2)
    {N : ℕ} (hN : I ^ N = ⊥) : W (k := k) x p = ⊤ := by
  have key : ∀ m : ℕ, (⊤ : Submodule k A) ≤ W (k := k) x p ⊔ (I ^ m).restrictScalars k := by
    intro m
    induction m with
    | zero =>
      intro a _
      refine Submodule.mem_sup_right ?_
      rw [Submodule.restrictScalars_mem, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ m ih =>
      intro a ha
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 (ih ha)
      rw [Submodule.restrictScalars_mem] at hz
      exact Submodule.add_mem _ (Submodule.mem_sup_left hw) (pow_le_W_sup hxp hgen m hz)
  refine eq_top_iff.2 fun a ha => ?_
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 (key N ha)
  rw [Submodule.restrictScalars_mem, hN, Ideal.mem_bot] at hz
  rw [hz, add_zero]
  exact hw

end System

section Construction

variable (k A)

noncomputable def proj : A →ₗ[k] ↥(I) where
  toFun a := ⟨a - ε a • (1 : A), sub_smul_one_mem a⟩
  map_add' a b := by
    ext
    simp only [map_add, Submodule.coe_add, add_smul]
    abel
  map_smul' c a := by
    ext
    simp only [map_smul, RingHom.id_apply, Submodule.coe_smul_of_tower, smul_sub, smul_eq_mul,
      mul_smul]

noncomputable def toCot : ↥(I) →ₗ[k] (I).Cotangent := (I).toCotangent.restrictScalars k

variable {k A}

theorem toCot_apply (u : ↥(I)) : toCot k A u = (I).toCotangent u := rfl

theorem proj_apply_of_mem {a : A} (ha : a ∈ I) : proj k A a = ⟨a, ha⟩ := by
  ext
  change a - ε a • (1 : A) = a
  rw [(mem_augIdeal_iff a).1 ha, zero_smul, sub_zero]

theorem isSystem_of_basis {r : ℕ} (b : Module.Basis (Fin r) k (I).Cotangent)
    (x : Fin r → A) (hxI : ∀ i, x i ∈ I) (hxb : ∀ i, (I).toCotangent ⟨x i, hxI i⟩ = b i) :
    IsSystem x (fun i => (b.coord i) ∘ₗ toCot k A ∘ₗ proj k A) := by
  refine ⟨hxI, fun i => ⟨?_, fun u hu v hv => ?_⟩, fun i j => ?_⟩
  ·
    simp only [LinearMap.comp_apply]
    have : proj k A 1 = 0 := by
      ext
      change (1 : A) - ε (1 : A) • (1 : A) = 0
      rw [Bialgebra.counit_one, one_smul, sub_self]
    rw [this, map_zero, map_zero]
  ·
    simp only [LinearMap.comp_apply]
    rw [proj_apply_of_mem (Ideal.mul_mem_left _ _ hv), toCot_apply,
      (Ideal.toCotangent_eq_zero _ _).2 (by rw [pow_two]; exact Ideal.mul_mem_mul hu hv), map_zero]
  ·
    simp only [LinearMap.comp_apply]
    rw [proj_apply_of_mem (hxI j), toCot_apply, hxb j, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]

theorem exists_sub_sum_mem_sq {r : ℕ} (b : Module.Basis (Fin r) k (I).Cotangent)
    (x : Fin r → A) (hxI : ∀ i, x i ∈ I) (hxb : ∀ i, (I).toCotangent ⟨x i, hxI i⟩ = b i)
    (u : A) (hu : u ∈ I) : ∃ c : Fin r → k, u - ∑ i, c i • x i ∈ I ^ 2 := by
  refine ⟨fun i => b.repr ((I).toCotangent ⟨u, hu⟩) i, ?_⟩
  have hsum : (I).toCotangent (⟨u, hu⟩ - ∑ i, (b.repr ((I).toCotangent ⟨u, hu⟩) i) • ⟨x i, hxI i⟩) = 0 := by
    rw [map_sub, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr ((I).toCotangent ⟨u, hu⟩)]
    rw [← toCot_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul_of_tower, toCot_apply, hxb]
  rw [Ideal.toCotangent_eq_zero] at hsum
  convert hsum using 1
  simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul_of_tower]

end Construction

theorem finrank_eq (p : ℕ) [Fact p.Prime] [CharP k p] [Module.Finite k A]
    (hA : ∀ a : A, ε a = 0 → a ^ p = 0) :
    Module.finrank k A = p ^ Module.finrank k (I).Cotangent := by
  classical

  haveI : IsNoetherian k A := inferInstance
  haveI : IsNoetherianRing A := isNoetherian_of_tower k inferInstance
  haveI : Module.Finite k (I).Cotangent := by
    refine Module.Finite.of_surjective ((toCot k A) ∘ₗ (proj k A)) fun c => ?_
    obtain ⟨u, rfl⟩ := (I).toCotangent_surjective c
    refine ⟨(u : A), ?_⟩
    rw [LinearMap.comp_apply, proj_apply_of_mem u.2, toCot_apply]

  set r := Module.finrank k (I).Cotangent
  let b : Module.Basis (Fin r) k (I).Cotangent := Module.finBasis k _
  have hlift : ∀ i, ∃ u : ↥(I), (I).toCotangent u = b i := fun i => (I).toCotangent_surjective (b i)
  choose xs hxs using hlift
  let x : Fin r → A := fun i => (xs i : A)
  have hxI : ∀ i, x i ∈ I := fun i => (xs i).2
  have hxb : ∀ i, (I).toCotangent ⟨x i, hxI i⟩ = b i := fun i => hxs i
  have hsys := isSystem_of_basis b x hxI hxb

  have hli := linearIndependent_mono (p := p) hsys
  have hxp : ∀ i, x i ^ p = 0 := fun i => hA _ ((mem_augIdeal_iff _).1 (hxI i))
  have hnil : IsNilpotent (I) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact ⟨p, hA a ((mem_augIdeal_iff a).1 ha)⟩
  obtain ⟨N, hN⟩ := hnil
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hsp := W_eq_top (k := k) hxp (exists_sub_sum_mem_sq b x hxI hxb) hN
  have htop : ⊤ ≤ Submodule.span k (Set.range fun ν : Fin r → Fin p => mono x (nat ν)) := by
    rw [← hsp]; exact le_rfl
  let B : Module.Basis (Fin r → Fin p) k A := Module.Basis.mk hli htop
  rw [Module.finrank_eq_card_basis B, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end HopfAlgebra.HeightOne
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero.HopfAlgebra P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero.HopfAlgebra.HeightOne"
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero.HopfAlgebra"

universe u v in

theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] [Module.Finite k A]
    (hA : ∀ a : A, Coalgebra.counit (R := k) a = 0 → a ^ p = 0) :
    Module.finrank k A =
      p ^ Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent :=
  HopfAlgebra.HeightOne.finrank_eq p hA

end S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
end P2MW
export P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero (solution)
