-- Prove2me | solution 1 for IsLocalRing.exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b09459b3-d200-5804-ac56-d24f33bac2ca

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair

set_option autoImplicit false

open IsLocalRing Finset

set_option maxHeartbeats 3200000 in
theorem solution
    {W R : Type*} [CommRing W] [CommRing R] [IsLocalRing R] [Algebra W R]
    (y₀ y₁ : R) (hmax : maximalIdeal R = Ideal.span {y₀, y₁})
    (hres : ∀ r : R, ∃ w : W, r - algebraMap W R w ∈ maximalIdeal R)
    (J : Ideal R) (D : ℕ) (h₀ : y₀ ^ D ∈ J) (h₁ : y₁ ^ D ∈ J) (r : R) :
    ∃ c : ℕ × ℕ → W,
      r - ∑ p ∈ Finset.range D ×ˢ Finset.range D, algebraMap W R (c p) * (y₀ ^ p.1 * y₁ ^ p.2) ∈ J := by
  classical

  let mono : ℕ × ℕ → R := fun p => y₀ ^ p.1 * y₁ ^ p.2
  let box : ℕ → Finset (ℕ × ℕ) := fun m => range m ×ˢ range m
  have hbox : ∀ m (p : ℕ × ℕ), p ∈ box m ↔ p.1 < m ∧ p.2 < m := by
    intro m p; simp [box, mem_product, mem_range]

  have hstep : ∀ r : R, ∃ (w : W) (r₀ r₁ : R), r = algebraMap W R w + y₀ * r₀ + y₁ * r₁ := by
    intro r
    obtain ⟨w, hw⟩ := hres r
    rw [hmax, Ideal.mem_span_pair] at hw
    obtain ⟨a, b, hab⟩ := hw
    exact ⟨w, a, b, by rw [mul_comm y₀, mul_comm y₁, add_assoc, hab]; ring⟩

  have hexp : ∀ (m : ℕ) (r : R), ∃ c : ℕ × ℕ → W, r - ∑ p ∈ box m, algebraMap W R (c p) * mono p ∈ maximalIdeal R ^ m := by
    intro m
    induction m with
    | zero => intro r; exact ⟨fun _ => 0, by simp [box]⟩
    | succ m ih =>
      intro r
      obtain ⟨w, r₀, r₁, hr⟩ := hstep r
      obtain ⟨c₀, hc₀⟩ := ih r₀
      obtain ⟨c₁, hc₁⟩ := ih r₁

      let c : ℕ × ℕ → W := fun p =>
        (if p = (0, 0) then w else 0) +
        (if 1 ≤ p.1 ∧ p.2 < m then c₀ (p.1 - 1, p.2) else 0) +
        (if 1 ≤ p.2 ∧ p.1 < m then c₁ (p.1, p.2 - 1) else 0)
      refine ⟨c, ?_⟩

      have hsumw : ∑ p ∈ box (m + 1), algebraMap W R (if p = (0, 0) then w else 0) * mono p = algebraMap W R w := by
        rw [Finset.sum_eq_single (0, 0)]
        · simp [mono]
        · intro p _ hp; simp [hp]
        · intro h; exact absurd ((hbox _ _).mpr ⟨Nat.succ_pos m, Nat.succ_pos m⟩) h
      have hsum0 : ∑ p ∈ box (m + 1), algebraMap W R (if 1 ≤ p.1 ∧ p.2 < m then c₀ (p.1 - 1, p.2) else 0) * mono p =
          y₀ * ∑ p ∈ box m, algebraMap W R (c₀ p) * mono p := by
        simp only [box, Finset.sum_product]
        rw [Finset.sum_range_succ']

        have h0 : ∑ b ∈ range (m + 1), algebraMap W R (if 1 ≤ ((0 : ℕ), b).1 ∧ ((0 : ℕ), b).2 < m then c₀ (((0:ℕ), b).1 - 1, ((0:ℕ), b).2) else 0) * mono ((0 : ℕ), b) = 0 := by
          refine Finset.sum_eq_zero fun b _ => ?_
          simp
        rw [h0, add_zero, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_range_succ, Finset.mul_sum]
        have hlast : algebraMap W R (if 1 ≤ (a + 1, m).1 ∧ (a + 1, m).2 < m then c₀ ((a + 1, m).1 - 1, (a + 1, m).2) else 0) * mono (a + 1, m) = 0 := by
          simp
        rw [hlast, add_zero]
        refine Finset.sum_congr rfl fun b hb => ?_
        have hb' : b < m := mem_range.mp hb
        simp only [Nat.le_add_left, hb', and_self, if_true, Nat.add_sub_cancel, mono]
        ring
      have hsum1 : ∑ p ∈ box (m + 1), algebraMap W R (if 1 ≤ p.2 ∧ p.1 < m then c₁ (p.1, p.2 - 1) else 0) * mono p =
          y₁ * ∑ p ∈ box m, algebraMap W R (c₁ p) * mono p := by
        simp only [box, Finset.sum_product]
        rw [Finset.sum_range_succ, Finset.mul_sum]
        have hlast : ∑ b ∈ range (m + 1), algebraMap W R (if 1 ≤ (m, b).2 ∧ (m, b).1 < m then c₁ ((m, b).1, (m, b).2 - 1) else 0) * mono (m, b) = 0 := by
          refine Finset.sum_eq_zero fun b _ => ?_
          simp
        rw [hlast, add_zero]
        refine Finset.sum_congr rfl fun a ha => ?_
        have ha' : a < m := mem_range.mp ha
        rw [Finset.sum_range_succ', Finset.mul_sum]
        have h0 : algebraMap W R (if 1 ≤ (a, 0).2 ∧ (a, 0).1 < m then c₁ ((a, 0).1, (a, 0).2 - 1) else 0) * mono (a, 0) = 0 := by simp
        rw [h0, add_zero]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [Nat.le_add_left, ha', and_self, if_true, Nat.add_sub_cancel, mono]
        ring
      have hsum : ∑ p ∈ box (m + 1), algebraMap W R (c p) * mono p =
          algebraMap W R w + y₀ * ∑ p ∈ box m, algebraMap W R (c₀ p) * mono p + y₁ * ∑ p ∈ box m, algebraMap W R (c₁ p) * mono p := by
        simp only [c, map_add, add_mul, Finset.sum_add_distrib]
        rw [hsumw, hsum0, hsum1]
      rw [hsum]
      have : r - (algebraMap W R w + y₀ * ∑ p ∈ box m, algebraMap W R (c₀ p) * mono p + y₁ * ∑ p ∈ box m, algebraMap W R (c₁ p) * mono p) =
          y₀ * (r₀ - ∑ p ∈ box m, algebraMap W R (c₀ p) * mono p) + y₁ * (r₁ - ∑ p ∈ box m, algebraMap W R (c₁ p) * mono p) := by
        rw [hr]; ring
      rw [this, pow_succ']
      have hy₀ : y₀ ∈ maximalIdeal R := by rw [hmax]; exact Ideal.subset_span (by simp)
      have hy₁ : y₁ ∈ maximalIdeal R := by rw [hmax]; exact Ideal.subset_span (by simp)
      exact add_mem (Ideal.mul_mem_mul hy₀ hc₀) (Ideal.mul_mem_mul hy₁ hc₁)

  have hpow : maximalIdeal R ^ (D + D) ≤ J := by
    have hm : maximalIdeal R = Ideal.span {y₀} ⊔ Ideal.span {y₁} := by
      rw [hmax, ← Ideal.span_union]; congr
    rw [hm]
    refine le_trans Ideal.sup_pow_add_le_pow_sup_pow (sup_le ?_ ?_)
    · rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]; exact h₀
    · rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]; exact h₁
  obtain ⟨c, hc⟩ := hexp (D + D) r
  refine ⟨c, ?_⟩

  have hsub : box D ⊆ box (D + D) := by
    intro p hp; rw [hbox] at hp ⊢; omega
  have hrest : ∑ p ∈ box (D + D) \ box D, algebraMap W R (c p) * mono p ∈ J := by
    refine Ideal.sum_mem _ fun p hp => ?_
    rw [Finset.mem_sdiff, hbox, hbox] at hp
    obtain ⟨-, hp2⟩ := hp
    refine Ideal.mul_mem_left _ _ ?_
    by_cases h : D ≤ p.1
    · have : mono p = y₀ ^ D * (y₀ ^ (p.1 - D) * y₁ ^ p.2) := by
        simp only [mono]; rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]
      rw [this]; exact Ideal.mul_mem_right _ _ h₀
    · have h' : D ≤ p.2 := by omega
      have : mono p = y₁ ^ D * (y₀ ^ p.1 * y₁ ^ (p.2 - D)) := by
        simp only [mono]; rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' h']
      rw [this]; exact Ideal.mul_mem_right _ _ h₁
  have hsplit : ∑ p ∈ box (D + D), algebraMap W R (c p) * mono p = ∑ p ∈ box D, algebraMap W R (c p) * mono p + ∑ p ∈ box (D + D) \ box D, algebraMap W R (c p) * mono p := by
    rw [← Finset.sum_sdiff hsub, add_comm]
  have : r - ∑ p ∈ box D, algebraMap W R (c p) * mono p = (r - ∑ p ∈ box (D + D), algebraMap W R (c p) * mono p) + ∑ p ∈ box (D + D) \ box D, algebraMap W R (c p) * mono p := by
    rw [hsplit]; ring
  show r - ∑ p ∈ box D, algebraMap W R (c p) * mono p ∈ J
  rw [this]
  exact add_mem (hpow hc) hrest

end S_IsLocalRing_exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair
end P2MW
export P2MW.S_IsLocalRing_exists_sub_sum_monomial_mem_of_maximalIdeal_eq_span_pair (solution)
