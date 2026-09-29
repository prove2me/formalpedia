-- Prove2me | solution 1 for IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/db40f35b-45dc-5afb-8441-4843c66585e2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal

set_option autoImplicit false

namespace NodeLiftEngine

open IsLocalRing Ideal

variable {A : Type*} [CommRing A]

theorem mem_span_pair_left (x y : A) : x ∈ Ideal.span ({x, y} : Set A) :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem mem_span_pair_right (x y : A) : y ∈ Ideal.span ({x, y} : Set A) :=
  Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem span_pair_le_iff {x y : A} {I : Ideal A} :
    Ideal.span ({x, y} : Set A) ≤ I ↔ x ∈ I ∧ y ∈ I := by
  rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  rfl

theorem span_pair_add_mul_eq (x y k : A) :
    Ideal.span ({x + k * y, y} : Set A) = Ideal.span {x, y} := by
  apply le_antisymm
  · rw [span_pair_le_iff]
    exact ⟨Ideal.mem_span_pair.mpr ⟨1, k, by ring⟩, mem_span_pair_right _ _⟩
  · rw [span_pair_le_iff]
    exact ⟨Ideal.mem_span_pair.mpr ⟨1, -k, by ring⟩, mem_span_pair_right _ _⟩

theorem span_pair_mul_isUnit_eq {x w : A} (hw : IsUnit w) (y : A) :
    Ideal.span ({x * w, y} : Set A) = Ideal.span {x, y} := by
  obtain ⟨w, rfl⟩ := hw
  apply le_antisymm
  · rw [span_pair_le_iff]
    exact ⟨Ideal.mem_span_pair.mpr ⟨(w : A), 0, by ring⟩, mem_span_pair_right _ _⟩
  · rw [span_pair_le_iff]
    refine ⟨Ideal.mem_span_pair.mpr ⟨((w⁻¹ : Aˣ) : A), 0, ?_⟩, mem_span_pair_right _ _⟩
    rw [zero_mul, add_zero, mul_comm x, ← mul_assoc, Units.inv_mul, one_mul]

theorem span_pair_pow_le {b ϖ : A} {Q : Ideal A} (hb : b ∈ Q) (hϖ : ϖ ∈ Q) {i : ℕ} (hi : 1 ≤ i) :
    Ideal.span ({b, ϖ ^ i} : Set A) ≤ Q := by
  rw [span_pair_le_iff]
  exact ⟨hb, Q.pow_mem_of_mem hϖ i hi⟩

section StepDown

variable {ϖ a b : A} {P : Ideal A}

theorem step_down (hϖ : ϖ ∈ nonZeroDivisors A) [P.IsPrime] (ha : Ideal.span {a, ϖ} = P)
    (hbP : b ∉ P) {M : ℕ} (hM : 1 ≤ M) {c : A} (hab : a * b = ϖ ^ M * c) {z : A}
    (hz : ϖ * z ∈ Ideal.span ({b, ϖ ^ M} : Set A)) :
    z ∈ Ideal.span ({b, ϖ ^ (M - 1)} : Set A) := by
  obtain ⟨w, y, hwy⟩ := Ideal.mem_span_pair.mp hz
  have hϖP : ϖ ∈ P := ha ▸ mem_span_pair_right a ϖ
  have hM' : ϖ ^ M = ϖ * ϖ ^ (M - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM]

  have hwb : w * b ∈ P := by
    have h1 : w * b = ϖ * z - y * ϖ ^ M := by linear_combination hwy
    rw [h1]
    exact P.sub_mem (P.mul_mem_right _ hϖP) (P.mul_mem_left _ (P.pow_mem_of_mem hϖP M hM))
  have hw : w ∈ P := ((‹P.IsPrime›).mem_or_mem hwb).resolve_right hbP
  rw [← ha] at hw
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hw

  have key : ϖ * z = ϖ * (α * ϖ ^ (M - 1) * c + β * b + y * ϖ ^ (M - 1)) := by
    have h2 : ϖ * z = α * (a * b) + β * ϖ * b + y * ϖ ^ M := by
      rw [← hwy, ← hαβ]; ring
    rw [h2, hab, hM']
    ring
  have hz' : z = α * ϖ ^ (M - 1) * c + β * b + y * ϖ ^ (M - 1) :=
    (mul_cancel_left_mem_nonZeroDivisors hϖ).mp key
  rw [hz']
  exact Ideal.mem_span_pair.mpr ⟨β, α * c + y, by ring⟩

theorem step_down_iter (hϖ : ϖ ∈ nonZeroDivisors A) [P.IsPrime] (ha : Ideal.span {a, ϖ} = P)
    (hbP : b ∉ P) {i : ℕ} :
    ∀ {M : ℕ}, i ≤ M → ∀ {c : A}, a * b = ϖ ^ M * c → ∀ {z : A},
      ϖ ^ i * z ∈ Ideal.span ({b, ϖ ^ M} : Set A) → z ∈ Ideal.span ({b, ϖ ^ (M - i)} : Set A) := by
  induction i with
  | zero =>
    intro M _ c _ z hz
    simpa using hz
  | succ i ih =>
    intro M hiM c hab z hz
    have hM : 1 ≤ M := le_trans (Nat.succ_le_succ (Nat.zero_le i)) hiM
    have h1 : ϖ * (ϖ ^ i * z) ∈ Ideal.span ({b, ϖ ^ M} : Set A) := by
      rw [← mul_assoc, ← pow_succ']; exact hz
    have h2 := step_down hϖ ha hbP hM hab h1
    have hab' : a * b = ϖ ^ (M - 1) * (ϖ * c) := by
      rw [hab, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hM]
    have h3 := ih (M := M - 1) (by omega) hab' h2
    have h4 : M - 1 - i = M - (i + 1) := by omega
    rwa [h4] at h3

end StepDown

section Witness

variable [IsLocalRing A] {ϖ a b : A} {P Q : Ideal A}

theorem no_deep_stage (hϖ : ϖ ∈ nonZeroDivisors A) [P.IsPrime] [Q.IsPrime]
    (ha : Ideal.span {a, ϖ} = P) (hb : Ideal.span {b, ϖ} = Q) (hbP : b ∉ P)
    {n : ℕ} {t t' : A} (htQ : t ∉ Q) (ht : t ∈ maximalIdeal A) (htt' : t * t' = ϖ ^ n)
    {c : A} (hab : a * b = ϖ ^ (n + 1) * c) : False := by
  classical
  have hbQ : b ∈ Q := hb ▸ mem_span_pair_left b ϖ
  have hϖQ : ϖ ∈ Q := hb ▸ mem_span_pair_right b ϖ
  have hQm : Q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hϖm : ϖ ∈ maximalIdeal A := hQm hϖQ

  set S : Finset ℕ := (Finset.range (n + 2)).filter (fun i => t' ∈ Ideal.span ({b, ϖ ^ i} : Set A))
    with hS
  have h0S : 0 ∈ S := by
    rw [hS, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [pow_zero]
    exact Ideal.mem_span_pair.mpr ⟨0, t', by ring⟩
  have hSne : S.Nonempty := ⟨0, h0S⟩
  set β : ℕ := S.max' hSne with hβdef
  have hβS : β ∈ S := Finset.max'_mem S hSne
  rw [hS, Finset.mem_filter, Finset.mem_range] at hβS
  obtain ⟨hβN, hβ⟩ := hβS
  have hmax : ∀ i, i ≤ n + 1 → t' ∈ Ideal.span ({b, ϖ ^ i} : Set A) → i ≤ β := by
    intro i hi hi'
    apply Finset.le_max'
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hi'⟩
  obtain ⟨x, t₀', hxt⟩ := Ideal.mem_span_pair.mp hβ

  have hprod : t * x * b + t * t₀' * ϖ ^ β = ϖ ^ n := by
    rw [← htt', ← hxt]; ring
  rcases le_or_gt β n with hβn | hβn
  ·
    have hnβ : ϖ ^ n = ϖ ^ β * ϖ ^ (n - β) := by
      rw [← pow_add, Nat.add_sub_cancel' hβn]
    have h1 : ϖ ^ β * (t * t₀' - ϖ ^ (n - β)) ∈ Ideal.span ({b, ϖ ^ (n + 1)} : Set A) := by
      have h2 : ϖ ^ β * (t * t₀' - ϖ ^ (n - β)) = (-(t * x)) * b + 0 * ϖ ^ (n + 1) := by
        have h3 : ϖ ^ β * (t * t₀') = ϖ ^ n - t * x * b := by linear_combination hprod
        rw [mul_sub, h3, ← hnβ]
        ring
      rw [h2]
      exact Ideal.mem_span_pair.mpr ⟨_, _, rfl⟩
    have h4 := step_down_iter hϖ ha hbP (i := β) (M := n + 1) (by omega) hab h1
    rcases hβn.lt_or_eq with hlt | heq
    ·
      have h5 : t * t₀' ∈ Q := by
        have h6 : t * t₀' - ϖ ^ (n - β) ∈ Q :=
          span_pair_pow_le hbQ hϖQ (i := n + 1 - β) (by omega) h4
        have h7 : ϖ ^ (n - β) ∈ Q := Q.pow_mem_of_mem hϖQ _ (by omega)
        simpa using Q.add_mem h6 h7
      have h8 : t₀' ∈ Q := ((‹Q.IsPrime›).mem_or_mem h5).resolve_left htQ
      rw [← hb] at h8
      obtain ⟨x', y', hxy'⟩ := Ideal.mem_span_pair.mp h8
      have h9 : t' ∈ Ideal.span ({b, ϖ ^ (β + 1)} : Set A) := by
        refine Ideal.mem_span_pair.mpr ⟨x + x' * ϖ ^ β, y', ?_⟩
        rw [← hxt, ← hxy', pow_succ]
        ring
      have := hmax (β + 1) (by omega) h9
      omega
    ·
      rw [heq, Nat.sub_self, pow_zero] at h4
      have h5 : t * t₀' - 1 ∈ maximalIdeal A :=
        hQm (span_pair_pow_le hbQ hϖQ (i := n + 1 - n) (by omega) h4)
      have h6 : t * t₀' ∉ maximalIdeal A := by
        intro h7
        have : (1 : A) ∈ maximalIdeal A := by simpa using (maximalIdeal A).sub_mem h7 h5
        exact (maximalIdeal A).ne_top_iff_one.mp (maximalIdeal.isMaximal A).ne_top this
      have h7 : IsUnit (t * t₀') := by
        by_contra h8
        exact h6 ((IsLocalRing.mem_maximalIdeal _).mpr h8)
      exact ((IsLocalRing.mem_maximalIdeal _).mp ht) (isUnit_of_mul_isUnit_left h7)
  ·
    have hnβ : ϖ ^ β = ϖ ^ n * ϖ ^ (β - n) := by
      rw [← pow_add, Nat.add_sub_cancel' hβn.le]
    have h1 : ϖ ^ n * (ϖ ^ (β - n) * (t * t₀') - 1) ∈ Ideal.span ({b, ϖ ^ (n + 1)} : Set A) := by
      have h2 : ϖ ^ n * (ϖ ^ (β - n) * (t * t₀') - 1) = (-(t * x)) * b + 0 * ϖ ^ (n + 1) := by
        have h3 : ϖ ^ β * (t * t₀') = ϖ ^ n - t * x * b := by linear_combination hprod
        rw [mul_sub, ← mul_assoc, ← hnβ, h3]
        ring
      rw [h2]
      exact Ideal.mem_span_pair.mpr ⟨_, _, rfl⟩
    have h4 := step_down_iter hϖ ha hbP (i := n) (M := n + 1) (by omega) hab h1
    rw [Nat.add_sub_cancel_left] at h4
    have h5 : ϖ ^ (β - n) * (t * t₀') - 1 ∈ maximalIdeal A :=
      hQm (span_pair_pow_le hbQ hϖQ (i := 1) le_rfl h4)
    have h6 : ϖ ^ (β - n) * (t * t₀') ∈ maximalIdeal A :=
      (maximalIdeal A).mul_mem_right _ ((maximalIdeal A).pow_mem_of_mem hϖm _ (by omega))
    have : (1 : A) ∈ maximalIdeal A := by simpa using (maximalIdeal A).sub_mem h6 h5
    exact (maximalIdeal A).ne_top_iff_one.mp (maximalIdeal.isMaximal A).ne_top this

end Witness

section Main

variable [IsLocalRing A]

theorem exists_mul_eq_pow
    {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A)
    {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hQP : ¬ Q ≤ P)
    (hPQ : P ⊔ Q = maximalIdeal A)
    {a b : A} (ha : Ideal.span {a, ϖ} = P) (hb : Ideal.span {b, ϖ} = Q)
    (hab : a * b ∈ Ideal.span ({ϖ} : Set A))
    {n : ℕ} {t t' : A} (htQ : t ∉ Q) (ht : t ∈ maximalIdeal A) (htt' : t * t' = ϖ ^ n) :
    ∃ (e : ℕ) (u v : A), 1 ≤ e ∧ e ≤ n ∧ u * v = ϖ ^ e ∧
      Ideal.span {u, ϖ} = P ∧ Ideal.span {v, ϖ} = Q := by
  by_contra H
  have hϖP : ϖ ∈ P := ha ▸ mem_span_pair_right a ϖ

  have stage : ∀ j : ℕ, 1 ≤ j → j ≤ n + 1 →
      ∃ a' b' c' : A, Ideal.span {a', ϖ} = P ∧ Ideal.span {b', ϖ} = Q ∧ a' * b' = ϖ ^ j * c' := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hab
      exact ⟨a, b, c, ha, hb, by rw [pow_one, ← hc, mul_comm]⟩
    | succ j hj ih =>
      intro hjn
      obtain ⟨a', b', c', ha', hb', hab'⟩ := ih (by omega)
      by_cases hc' : IsUnit c'
      ·
        obtain ⟨w, hw⟩ := hc'
        refine (H ⟨j, a', b' * ↑w⁻¹, hj, by omega, ?_, ha', ?_⟩).elim
        · rw [← mul_assoc, hab', ← hw, mul_assoc, Units.mul_inv, mul_one]
        · rw [span_pair_mul_isUnit_eq (Units.isUnit _), hb']
      ·
        have hcm : c' ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hc'
        rw [← hPQ, ← ha', ← hb'] at hcm
        obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hcm
        obtain ⟨α, γ₁, hαγ⟩ := Ideal.mem_span_pair.mp hp
        obtain ⟨β, γ₂, hβγ⟩ := Ideal.mem_span_pair.mp hq
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        refine ⟨a' - ϖ ^ (k + 1) * β, b' - ϖ ^ (k + 1) * α, γ₁ + γ₂ + ϖ ^ k * α * β, ?_, ?_, ?_⟩
        · have h1 : a' - ϖ ^ (k + 1) * β = a' + (-(ϖ ^ k * β)) * ϖ := by
            rw [pow_succ]; ring
          rw [h1, span_pair_add_mul_eq, ha']
        · have h1 : b' - ϖ ^ (k + 1) * α = b' + (-(ϖ ^ k * α)) * ϖ := by
            rw [pow_succ]; ring
          rw [h1, span_pair_add_mul_eq, hb']
        · have h1 : c' = α * a' + β * b' + (γ₁ + γ₂) * ϖ := by
            rw [← hpq, ← hαγ, ← hβγ]; ring
          have h4 : (a' - ϖ ^ (k + 1) * β) * (b' - ϖ ^ (k + 1) * α) =
              a' * b' - ϖ ^ (k + 1) * (α * a' + β * b') + ϖ ^ (k + 1) * ϖ ^ (k + 1) * (α * β) := by
            ring
          rw [h4, hab']
          conv_lhs => rw [h1]
          simp only [pow_succ]
          ring
  obtain ⟨a', b', c', ha', hb', hab'⟩ := stage (n + 1) (by omega) le_rfl
  have hbP : b' ∉ P := by
    intro h
    apply hQP
    rw [← hb', span_pair_le_iff]
    exact ⟨h, hϖP⟩
  exact no_deep_stage hϖ ha' hb' hbP htQ ht htt' hab'

end Main

end NodeLiftEngine

theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A]
    {ϖ : A} (hϖ : ϖ ∈ nonZeroDivisors A)
    {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hQP : ¬ Q ≤ P)
    (hPQ : P ⊔ Q = IsLocalRing.maximalIdeal A)
    {a b : A} (ha : Ideal.span {a, ϖ} = P) (hb : Ideal.span {b, ϖ} = Q)
    (hab : a * b ∈ Ideal.span {ϖ})
    {n : ℕ} {t t' : A} (htQ : t ∉ Q) (ht : t ∈ IsLocalRing.maximalIdeal A)
    (htt' : t * t' = ϖ ^ n) :
    ∃ (e : ℕ) (u v : A), 1 ≤ e ∧ e ≤ n ∧ u * v = ϖ ^ e ∧
      Ideal.span {u, ϖ} = P ∧ Ideal.span {v, ϖ} = Q :=
  NodeLiftEngine.exists_mul_eq_pow hϖ hQP hPQ ha hb hab htQ ht htt'

end S_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal
end P2MW
export P2MW.S_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal (solution)
