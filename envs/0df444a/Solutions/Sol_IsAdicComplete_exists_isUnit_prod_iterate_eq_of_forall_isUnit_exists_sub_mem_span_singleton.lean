-- Prove2me | solution 1 for IsAdicComplete.exists_isUnit_prod_iterate_eq_of_forall_isUnit_exists_sub_mem_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f50576e8-e61e-5bd3-8097-1f1f6c90b042

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAdicComplete_exists_isUnit_prod_iterate_eq_of_forall_isUnit_exists_sub_mem_span_singleton

set_option autoImplicit false

open Finset

namespace IsAdicComplete
p2m_export "IsAdicComplete" "toIsPrecomplete le_jacobson_bot toIsHausdorff"
namespace NormLift
p2m_open "IsAdicComplete"

variable {D : Type*} [CommRing D] (ϖ : D) (τ : D →+* D) (n : ℕ)

def nrm (u : D) : D := ∏ i ∈ range n, τ^[i] u

def trc (x : D) : D := ∑ i ∈ range n, τ^[i] x

variable {ϖ τ n}

theorem iterate_map_mul (i : ℕ) (x y : D) : τ^[i] (x * y) = τ^[i] x * τ^[i] y := by
  rw [← RingHom.coe_pow, map_mul]

theorem iterate_map_add (i : ℕ) (x y : D) : τ^[i] (x + y) = τ^[i] x + τ^[i] y := by
  rw [← RingHom.coe_pow, map_add]

theorem iterate_map_one (i : ℕ) : τ^[i] (1 : D) = 1 := by
  rw [← RingHom.coe_pow, map_one]

theorem iterate_fix {x : D} (hx : τ x = x) (i : ℕ) : τ^[i] x = x :=
  Function.iterate_fixed hx i

theorem nrm_mul (x y : D) : nrm τ n (x * y) = nrm τ n x * nrm τ n y := by
  simp only [nrm, iterate_map_mul, prod_mul_distrib]

theorem nrm_isUnit {x : D} (hx : IsUnit x) : IsUnit (nrm τ n x) := by
  unfold nrm
  refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun i _ => ?_
  rw [← RingHom.coe_pow]
  exact hx.map _

theorem trc_mul_of_fix (x : D) {a : D} (ha : τ a = a) : trc τ n (x * a) = trc τ n x * a := by
  simp only [trc, iterate_map_mul, iterate_fix ha, sum_mul]

theorem map_nrm (hτn : ∀ x, τ^[n] x = x) (x : D) : τ (nrm τ n x) = nrm τ n x := by
  unfold nrm
  rw [map_prod]
  have : ∀ i, τ (τ^[i] x) = τ^[i + 1] x := fun i => (Function.iterate_succ_apply' τ i x).symm
  simp_rw [this]
  cases n with
  | zero => simp
  | succ m =>
    rw [prod_range_succ, prod_range_succ', hτn]
    simp

theorem iterate_sub_mem {J : Ideal D} (hJ : ∀ x ∈ J, τ x ∈ J) {x y : D} (h : x - y ∈ J) (i : ℕ) :
    τ^[i] x - τ^[i] y ∈ J := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub]
    exact hJ _ ih

theorem nrm_sub_nrm_mem {J : Ideal D} (hJ : ∀ x ∈ J, τ x ∈ J) {x y : D} (h : x - y ∈ J) :
    nrm τ n x - nrm τ n y ∈ J := by
  rw [← Ideal.Quotient.eq]
  unfold nrm
  rw [map_prod, map_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [Ideal.Quotient.eq]
  exact iterate_sub_mem hJ h i

theorem span_pow_stable (hτϖ : τ ϖ = ϖ) (k : ℕ) : ∀ x ∈ Ideal.span {ϖ ^ k}, τ x ∈ Ideal.span {ϖ ^ k} := by
  intro x hx
  rw [Ideal.mem_span_singleton] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, hτϖ]
  exact dvd_mul_right _ _

theorem prod_one_add_sub_mem (k : ℕ) (s : Finset ℕ) (x : ℕ → D) :
    ∏ i ∈ s, (1 + ϖ ^ k * x i) - (1 + ϖ ^ k * ∑ i ∈ s, x i) ∈ Ideal.span {ϖ ^ (2 * k)} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    rw [Ideal.mem_span_singleton] at ih ⊢
    obtain ⟨y, hy⟩ := ih
    have : ∏ i ∈ s, (1 + ϖ ^ k * x i) = (1 + ϖ ^ k * ∑ i ∈ s, x i) + ϖ ^ (2 * k) * y := by
      rw [← hy]; ring
    rw [this]
    refine ⟨y + x a * (∑ i ∈ s, x i) + ϖ ^ k * x a * y, ?_⟩
    ring

end IsAdicComplete.NormLift

namespace IsAdicComplete
p2m_export "IsAdicComplete" "toIsPrecomplete le_jacobson_bot toIsHausdorff"
namespace NormLift
p2m_open "IsAdicComplete"

variable {D : Type*} [CommRing D]

section Main

variable (ϖ : D) (τ : D →+* D) (n : ℕ)
  (hreg : ϖ ∈ nonZeroDivisors D) (hτn : ∀ x, τ^[n] x = x) (hτϖ : τ ϖ = ϖ)
  (x₀ : D) (hx₀ : trc τ n x₀ - 1 ∈ Ideal.span {ϖ})
  (c : D) (hc : IsUnit c) (hτc : τ c = c)

include hreg hτn hτϖ hx₀ hc hτc in

theorem step [IsAdicComplete (Ideal.span {ϖ}) D] (P : D) (hP : IsUnit P) (k : ℕ)
    (hk : ϖ ^ (k + 1) ∣ nrm τ n P - c) :
    ∃ P' : D, IsUnit P' ∧ ϖ ^ (k + 1) ∣ P' - P ∧ ϖ ^ (k + 2) ∣ nrm τ n P' - c := by
  obtain ⟨e, he⟩ := hk
  obtain ⟨cu, rfl⟩ := hc
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 hx₀

  have hτe : τ e = e := by
    have h1 : τ (nrm τ n P - (cu : D)) = nrm τ n P - (cu : D) := by
      rw [map_sub, map_nrm hτn, hτc]
    rw [he, map_mul, map_pow, hτϖ] at h1
    have h2 : (τ e - e) * ϖ ^ (k + 1) = 0 := by rw [mul_comm, mul_sub, h1, sub_self]
    have h3 : ϖ ^ (k + 1) * (τ e - e) = 0 := by rw [mul_comm]; exact h2
    have hreg' : ϖ ^ (k + 1) ∈ nonZeroDivisors D := pow_mem hreg _
    exact sub_eq_zero.1 (hreg'.1 _ h3)

  have hτci : τ (↑cu⁻¹ : D) = ↑cu⁻¹ := by
    have h1 : τ (↑cu⁻¹ : D) * (cu : D) = 1 := by
      conv_lhs => rw [← hτc]
      rw [← map_mul, Units.inv_mul, map_one]
    calc τ (↑cu⁻¹ : D) = τ (↑cu⁻¹ : D) * ((cu : D) * ↑cu⁻¹) := by rw [Units.mul_inv, mul_one]
      _ = ↑cu⁻¹ := by rw [← mul_assoc, h1, one_mul]
  set a : D := -((↑cu⁻¹ : D) * e) with ha_def
  have hτa : τ a = a := by rw [ha_def, map_neg, map_mul, hτci, hτe]
  have hca : (cu : D) * a = -e := by
    rw [ha_def, mul_neg, ← mul_assoc, Units.mul_inv, one_mul]
  set x : D := x₀ * a with hx_def
  have hT : trc τ n x = (1 + ϖ * z) * a := by
    rw [hx_def, trc_mul_of_fix x₀ hτa]
    congr 1
    rw [← hz]; ring
  set w : D := 1 + ϖ ^ (k + 1) * x with hw_def
  have hwu : IsUnit w := by
    have hmem : ϖ ^ (k + 1) * x ∈ Ideal.span ({ϖ} : Set D) :=
      Ideal.mem_span_singleton.2 ⟨ϖ ^ k * x, by ring⟩
    have := Ideal.mem_jacobson_bot.1 (le_jacobson_bot (Ideal.span ({ϖ} : Set D)) hmem) 1
    rw [mul_one, add_comm] at this
    exact this

  have hnw : ∃ y, nrm τ n w = 1 + ϖ ^ (k + 1) * trc τ n x + ϖ ^ (2 * (k + 1)) * y := by
    have hfac : ∀ i, τ^[i] w = 1 + ϖ ^ (k + 1) * τ^[i] x := by
      intro i
      rw [hw_def, iterate_map_add, iterate_map_one, iterate_map_mul]
      congr 2
      refine iterate_fix ?_ i
      rw [map_pow, hτϖ]
    have h := prod_one_add_sub_mem (ϖ := ϖ) (k + 1) (range n) (fun i => τ^[i] x)
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 h
    refine ⟨y, ?_⟩
    unfold nrm trc
    simp_rw [hfac]
    exact sub_eq_iff_eq_add'.1 hy
  obtain ⟨y, hy⟩ := hnw
  refine ⟨P * w, hP.mul hwu, ⟨P * x, by rw [hw_def]; ring⟩, ?_⟩
  refine ⟨(cu : D) * z * a + ϖ ^ k * (e * ((1 + ϖ * z) * a)) + ϖ ^ k * ((cu : D) * y) +
    ϖ ^ (2 * k + 1) * (e * y), ?_⟩
  rw [nrm_mul, hy, hT, show nrm τ n P = (cu : D) + ϖ ^ (k + 1) * e from by rw [← he]; ring]
  linear_combination (ϖ ^ (k + 1)) * hca

end Main

end IsAdicComplete.NormLift

namespace IsAdicComplete
p2m_export "IsAdicComplete" "toIsPrecomplete le_jacobson_bot toIsHausdorff"
namespace NormLift
p2m_open "IsAdicComplete"

variable {D : Type*} [CommRing D]

section Limit

variable (ϖ : D) (τ : D →+* D) (n : ℕ)
  (hreg : ϖ ∈ nonZeroDivisors D) (hτn : ∀ x, τ^[n] x = x) (hτϖ : τ ϖ = ϖ)
  (x₀ : D) (hx₀ : trc τ n x₀ - 1 ∈ Ideal.span {ϖ})
  (c : D) (hc : IsUnit c) (hτc : τ c = c)

open scoped Classical in

noncomputable def seq [IsAdicComplete (Ideal.span {ϖ}) D] (u₀ : D) : ℕ → D
  | 0 => u₀
  | k + 1 =>
    if h : IsUnit (seq u₀ k) ∧ ϖ ^ (k + 1) ∣ nrm τ n (seq u₀ k) - c then
      Classical.choose (step ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc (seq u₀ k) h.1 k h.2)
    else seq u₀ k

variable [IsAdicComplete (Ideal.span {ϖ}) D] (u₀ : D) (hu₀ : IsUnit u₀)
  (hu₀c : ϖ ∣ nrm τ n u₀ - c)

include hu₀ hu₀c in
theorem seq_spec (k : ℕ) :
    IsUnit (seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ k) ∧
      ϖ ^ (k + 1) ∣ nrm τ n (seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ k) - c := by
  induction k with
  | zero => exact ⟨hu₀, by simp at hu₀c ⊢; exact hu₀c⟩
  | succ k ih =>
    have hs : seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ (k + 1) =
        Classical.choose (step ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc _ ih.1 k ih.2) := by
      rw [seq, dif_pos ih]
    have hspec := Classical.choose_spec (step ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc _ ih.1 k ih.2)
    rw [hs]
    exact ⟨hspec.1, hspec.2.2⟩

include hu₀ hu₀c in
theorem seq_succ_sub (k : ℕ) :
    ϖ ^ (k + 1) ∣ seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ (k + 1) -
      seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ k := by
  have ih := seq_spec ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ hu₀ hu₀c k
  have hs : seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ (k + 1) =
      Classical.choose (step ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc _ ih.1 k ih.2) := by
    rw [seq, dif_pos ih]
  rw [hs]
  exact (Classical.choose_spec (step ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc _ ih.1 k ih.2)).2.1

include hu₀ hu₀c in
theorem seq_sub_mem {m k : ℕ} (hmk : m ≤ k) :
    seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ k - seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ m ∈
      Ideal.span {ϖ ^ m} := by
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    have h1 := seq_succ_sub ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ hu₀ hu₀c k
    have h2 : ϖ ^ m ∣ seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ (k + 1) -
        seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ k :=
      (pow_dvd_pow ϖ (by omega)).trans h1
    rw [Ideal.mem_span_singleton] at ih ⊢
    have := dvd_add h2 ih
    rwa [sub_add_sub_cancel] at this

include hreg hτn hτϖ hx₀ hc hτc hu₀ hu₀c in

theorem exists_isUnit_nrm_eq : ∃ u : D, IsUnit u ∧ nrm τ n u = c := by
  set f : ℕ → D := seq ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ with hf_def
  have hI : ∀ m : ℕ, (Ideal.span ({ϖ} : Set D) ^ m • ⊤ : Submodule D D) = Ideal.span {ϖ ^ m} := by
    intro m
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have hf : ∀ {m k : ℕ}, m ≤ k → f m ≡ f k [SMOD (Ideal.span ({ϖ} : Set D) ^ m • ⊤ : Submodule D D)] := by
    intro m k hmk
    rw [hI, SModEq.sub_mem, ← Ideal.neg_mem_iff, neg_sub]
    exact seq_sub_mem ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ hu₀ hu₀c hmk
  obtain ⟨u, hu⟩ := IsPrecomplete.prec
    (IsAdicComplete.toIsPrecomplete : IsPrecomplete (Ideal.span ({ϖ} : Set D)) D) hf
  have hu' : ∀ k, f k - u ∈ Ideal.span {ϖ ^ k} := fun k => by
    have := hu k
    rwa [hI, SModEq.sub_mem] at this
  refine ⟨u, ?_, ?_⟩
  ·
    have h1 := hu' 1
    rw [pow_one, Ideal.mem_span_singleton] at h1
    obtain ⟨t, ht⟩ := h1
    obtain ⟨f1, hf1⟩ := (seq_spec ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ hu₀ hu₀c 1).1
    rw [← hf_def] at hf1
    have hu_eq : u = (f1 : D) * (1 + ϖ * (-(↑f1⁻¹ * t))) := by
      have : u = f 1 - ϖ * t := by rw [← ht]; ring
      rw [this, ← hf1]
      have hfi : (f1 : D) * ↑f1⁻¹ = 1 := Units.mul_inv f1
      linear_combination (ϖ * t) * hfi
    rw [hu_eq]
    refine (Units.isUnit f1).mul ?_
    have hmem : ϖ * (-(↑f1⁻¹ * t)) ∈ Ideal.span ({ϖ} : Set D) :=
      Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    have := Ideal.mem_jacobson_bot.1 (le_jacobson_bot (Ideal.span ({ϖ} : Set D)) hmem) 1
    rwa [mul_one, add_comm] at this
  ·
    rw [← sub_eq_zero]
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff : IsHausdorff (Ideal.span ({ϖ} : Set D)) D)
    intro k
    rw [hI, SModEq.zero]
    have h1 : nrm τ n u - nrm τ n (f k) ∈ Ideal.span {ϖ ^ k} := by
      apply nrm_sub_nrm_mem (span_pow_stable hτϖ k)
      rw [← Ideal.neg_mem_iff, neg_sub]
      exact hu' k
    have h2 : nrm τ n (f k) - c ∈ Ideal.span {ϖ ^ k} := by
      rw [Ideal.mem_span_singleton]
      exact (pow_dvd_pow ϖ (Nat.le_succ k)).trans
        (seq_spec ϖ τ n hreg hτn hτϖ x₀ hx₀ c hc hτc u₀ hu₀ hu₀c k).2
    have := Ideal.add_mem _ h1 h2
    rwa [sub_add_sub_cancel] at this

end Limit

end IsAdicComplete.NormLift

open IsAdicComplete.NormLift in
theorem solution
    {D : Type*} [CommRing D] (ϖ : D) (hϖ : ϖ ∈ nonZeroDivisors D)
    [IsAdicComplete (Ideal.span {ϖ}) D]
    (τ : D →+* D) (n : ℕ) (hτn : ∀ x, τ^[n] x = x) (hτϖ : τ ϖ = ϖ)
    (hT : ∃ x₀ : D, (∑ i ∈ Finset.range n, τ^[i] x₀) - 1 ∈ Ideal.span {ϖ})
    (hN : ∀ c : D, IsUnit c → τ c = c →
      ∃ u : D, IsUnit u ∧ (∏ i ∈ Finset.range n, τ^[i] u) - c ∈ Ideal.span {ϖ})
    (c : D) (hc : IsUnit c) (hτc : τ c = c) :
    ∃ u : D, IsUnit u ∧ (∏ i ∈ Finset.range n, τ^[i] u) = c := by
  obtain ⟨x₀, hx₀⟩ := hT
  obtain ⟨u₀, hu₀, hu₀c⟩ := hN c hc hτc
  rw [Ideal.mem_span_singleton] at hu₀c
  exact exists_isUnit_nrm_eq ϖ τ n hϖ hτn hτϖ x₀ hx₀ c hc hτc u₀ hu₀ hu₀c

end S_IsAdicComplete_exists_isUnit_prod_iterate_eq_of_forall_isUnit_exists_sub_mem_span_singleton
end P2MW
export P2MW.S_IsAdicComplete_exists_isUnit_prod_iterate_eq_of_forall_isUnit_exists_sub_mem_span_singleton (solution)
