-- Prove2me | solution 1 for LenstraIP.Rounding.rounding_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T07:07:45.518571+00:00
-- url     : https://prove2.me/submissions/81bc630c-7655-4a7b-9e2d-514a95cf108a

import Mathlib
import Definitions.Def_LenstraIP_Rounding_SimplexData

set_option autoImplicit false

namespace LenstraRoundHelp

open LenstraIP.Rounding

/-- Gram matrix of a regular simplex about its centroid. -/
theorem gram {n : ℕ} (w : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) (s a : ℝ)
    (ha : a = s ^ 2 / (2 * ((n : ℝ) + 1)))
    (hs : ∀ i j, i ≠ j → dist (w i) (w j) = s) (i j : Fin (n + 1)) :
    inner ℝ (w i - centroid w) (w j - centroid w) = if i = j then (n : ℝ) * a else -a := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  set p := centroid w with hp
  set u : Fin (n + 1) → EuclideanSpace ℝ (Fin n) := fun k => w k - p with hu
  have hsum : ∑ k, u k = 0 := by
    simp only [hu, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, hp, centroid, smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hn1, one_smul, sub_self]
  have hd : ∀ i j, ‖u i - u j‖ ^ 2 = if i = j then 0 else s ^ 2 := by
    intro i j
    split_ifs with h
    · subst h; simp
    · rw [show u i - u j = w i - w j by simp [hu], ← dist_eq_norm, hs i j h]
  have hrow : ∀ i, ((n : ℝ) + 1) * ‖u i‖ ^ 2 + ∑ k, ‖u k‖ ^ 2 = n * s ^ 2 := by
    intro i
    have h1 : ∑ k, ‖u i - u k‖ ^ 2 = n * s ^ 2 := by
      have e : ∀ k, ‖u i - u k‖ ^ 2 = s ^ 2 - if i = k then s ^ 2 else 0 := by
        intro k; rw [hd]; split_ifs <;> ring
      simp_rw [e]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
      simp; ring
    have h2 : ∀ k, ‖u i - u k‖ ^ 2 = ‖u i‖ ^ 2 - 2 * inner ℝ (u i) (u k) + ‖u k‖ ^ 2 :=
      fun k => norm_sub_sq_real _ _
    have h3 : ∑ k, inner ℝ (u i) (u k) = 0 := by
      rw [← inner_sum, hsum, inner_zero_right]
    simp_rw [h2] at h1
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h3] at h1
    simp at h1
    linarith
  have hS : ∑ k, ‖u k‖ ^ 2 = n * s ^ 2 / 2 := by
    have h := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hrow i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    simp at h
    have h' : ((n : ℝ) + 1) * (2 * ∑ k, ‖u k‖ ^ 2 - n * s ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hn1
    · linarith
  have hN : ∀ i, ‖u i‖ ^ 2 = n * a := by
    intro i
    have := hrow i
    rw [hS] at this
    rw [ha]; field_simp; linarith
  change inner ℝ (u i) (u j) = _
  split_ifs with h
  · subst h; rw [real_inner_self_eq_norm_sq, hN]
  · have e := norm_sub_sq_real (u i) (u j)
    rw [hd i j, if_neg h, hN, hN] at e
    have : s ^ 2 = 2 * ((n : ℝ) + 1) * a := by rw [ha]; field_simp
    linarith

theorem sumsq_bound (n : ℕ) (hn : 1 ≤ n) (l : Fin (n + 1) → ℝ) (hsum : ∑ i, l i = 1)
    (hb : ∀ i, |l i| ≤ 3 / 2) :
    ((n : ℝ) + 1) * ∑ i, l i ^ 2 - 1 ≤ 4 * (n : ℝ) ^ 2 := by
  have hsq : ∀ i, l i ^ 2 ≤ 9 / 4 := by
    intro i; have h1 := abs_le.mp (hb i); nlinarith [h1.1, h1.2]
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h | h | h
  · subst h
    simp [Fin.sum_univ_two] at hsum ⊢
    have h0 := abs_le.mp (hb 0); have h1 := abs_le.mp (hb 1)
    nlinarith [mul_nonneg (sub_nonneg.2 h0.2) (sub_nonneg.2 h1.2)]
  · subst h
    simp [Fin.sum_univ_three] at hsum ⊢
    have h0 := abs_le.mp (hb 0); have h1 := abs_le.mp (hb 1); have h2 := abs_le.mp (hb 2)
    nlinarith [mul_nonneg (sub_nonneg.2 h0.2) (sub_nonneg.2 h1.2),
      mul_nonneg (sub_nonneg.2 h0.2) (sub_nonneg.2 h2.2),
      mul_nonneg (sub_nonneg.2 h1.2) (sub_nonneg.2 h2.2),
      mul_nonneg (sub_nonneg.2 h0.2) (neg_le_iff_add_nonneg.1 h1.1),
      mul_nonneg (sub_nonneg.2 h0.2) (neg_le_iff_add_nonneg.1 h2.1),
      mul_nonneg (sub_nonneg.2 h1.2) (neg_le_iff_add_nonneg.1 h0.1),
      mul_nonneg (sub_nonneg.2 h1.2) (neg_le_iff_add_nonneg.1 h2.1),
      mul_nonneg (sub_nonneg.2 h2.2) (neg_le_iff_add_nonneg.1 h0.1),
      mul_nonneg (sub_nonneg.2 h2.2) (neg_le_iff_add_nonneg.1 h1.1),
      mul_nonneg (neg_le_iff_add_nonneg.1 h0.1) (neg_le_iff_add_nonneg.1 h1.1),
      mul_nonneg (neg_le_iff_add_nonneg.1 h0.1) (neg_le_iff_add_nonneg.1 h2.1),
      mul_nonneg (neg_le_iff_add_nonneg.1 h1.1) (neg_le_iff_add_nonneg.1 h2.1)]
  · have hs : ∑ i, l i ^ 2 ≤ ((n : ℝ) + 1) * (9 / 4) := by
      calc ∑ i, l i ^ 2 ≤ ∑ _i : Fin (n + 1), (9 / 4 : ℝ) := Finset.sum_le_sum (fun i _ => hsq i)
        _ = _ := by simp
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs hn1]

end LenstraRoundHelp

open LenstraIP.Rounding in
theorem solution {n : ℕ} (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : Convex ℝ K)
    (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) (hv : AffineIndependent ℝ v)
    (hvK : ∀ j, v j ∈ K)
    (g : Fin (n + 1) → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ))
    (hg_const : ∀ i j k, j ≠ i → k ≠ i → g i (v j) = g i (v k))
    (hg_ne : ∀ i j, j ≠ i → g i (v i) ≠ g i (v j))
    (h16 : ∀ x ∈ K, ∀ i j, i ≠ j → |g i (x - v j)| ≤ 3 / 2 * |g i (v i - v j)|)
    (τ : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hτ : IsRegular (τ ∘ v)) :
    ∃ r R : ℝ, 0 < r ∧ 0 < R ∧
      Metric.closedBall (centroid (τ ∘ v)) r ⊆ τ '' K ∧
      τ '' K ⊆ Metric.closedBall (centroid (τ ∘ v)) R ∧
      R / r ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  obtain ⟨s, hs0, hs⟩ := hτ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set a : ℝ := s ^ 2 / (2 * ((n : ℝ) + 1)) with ha
  have ha0 : 0 < a := by positivity
  have hG := LenstraRoundHelp.gram (τ ∘ v) s a ha hs
  set p := centroid (τ ∘ v) with hp
  simp only [Function.comp_apply] at hG
  have hspan : affineSpan ℝ (Set.range v) = ⊤ := by
    rw [hv.affineSpan_eq_top_iff_card_eq_finrank_add_one]; simp
  let b : AffineBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin n)) := ⟨v, hv, hspan⟩
  have hrep : ∀ x, ∑ k, b.coord k x • v k = x := fun x => b.linear_combination_coord_eq_self x
  have hone : ∀ x, ∑ k, b.coord k x = 1 := fun x => b.sum_coord_apply_eq_one x
  have hτrep : ∀ x, τ x - p = ∑ k, b.coord k x • (τ (v k) - p) := by
    intro x
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hone, one_smul]
    congr 1
    conv_lhs => rw [← hrep x]
    simp [map_sum, map_smul]
  have hinner : ∀ x m, inner ℝ (τ x - p) (τ (v m) - p) = a * (((n : ℝ) + 1) * b.coord m x - 1) := by
    intro x m
    rw [hτrep x, sum_inner]
    simp_rw [real_inner_smul_left, hG]
    have e : ∀ k, b.coord k x * (if k = m then (n : ℝ) * a else -a) =
        -a * b.coord k x + (if k = m then ((n : ℝ) + 1) * a * b.coord k x else 0) := by
      intro k; split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hone, Finset.sum_ite_eq']
    simp; ring
  have hcoordK : ∀ x ∈ K, ∀ i, |b.coord i x| ≤ 3 / 2 := by
    intro x hx i
    obtain ⟨j, hji⟩ : ∃ j : Fin (n + 1), j ≠ i := by
      by_cases h : i = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩; subst h; simp [Fin.ext_iff]
      · exact ⟨0, Ne.symm h⟩
    have hxj : x - v j = ∑ k, b.coord k x • (v k - v j) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hone, one_smul]
      rw [hrep x]
    have hg : g i (x - v j) = b.coord i x * g i (v i - v j) := by
      rw [hxj, map_sum, Finset.sum_eq_single i]
      · rw [map_smul, smul_eq_mul]
      · intro k _ hki
        rw [map_smul, map_sub, hg_const i k j hki hji, sub_self, smul_zero]
      · simp
    have hc : g i (v i - v j) ≠ 0 := by
      rw [map_sub, sub_ne_zero]; exact (hg_ne i j hji)
    have h := h16 x hx i j (Ne.symm hji)
    rw [hg, abs_mul] at h
    exact le_of_mul_le_mul_right h (abs_pos.mpr hc)
  have hu2 : ∀ m, ‖τ (v m) - p‖ ^ 2 = n * a := by
    intro m; rw [← real_inner_self_eq_norm_sq, hG, if_pos rfl]
  set t := Real.sqrt (a / n) with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t ^ 2 = a / n := Real.sq_sqrt (by positivity)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  refine ⟨t, 2 * n * Real.sqrt n * t, ht0, by positivity, ?_, ?_, ?_⟩
  · intro y hy
    rw [Metric.mem_closedBall] at hy
    refine ⟨τ.symm y, ?_, by simp⟩
    set x := τ.symm y with hx
    have hy' : τ x = y := by simp [hx]
    have hnn : ∀ m, 0 ≤ b.coord m x := by
      intro m
      have h1 := hinner x m
      have hcs : |inner ℝ (τ x - p) (τ (v m) - p)| ≤ ‖τ x - p‖ * ‖τ (v m) - p‖ :=
        abs_real_inner_le_norm _ _
      have hd : ‖τ x - p‖ ≤ t := by rw [hy', ← dist_eq_norm]; exact hy
      have hprod : t * ‖τ (v m) - p‖ = a := by
        have h0 : 0 ≤ t * ‖τ (v m) - p‖ := by positivity
        have hsq : (t * ‖τ (v m) - p‖) ^ 2 = a ^ 2 := by
          rw [mul_pow, ht2, hu2]; field_simp
        nlinarith
      have hle : ‖τ x - p‖ * ‖τ (v m) - p‖ ≤ a := by
        rw [← hprod]; exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      have hl := (abs_le.mp (hcs.trans hle)).1
      rw [h1] at hl
      have h2 : 0 ≤ a * (((n : ℝ) + 1) * b.coord m x) := by nlinarith
      have h3 := (mul_nonneg_iff_of_pos_left ha0).mp h2
      exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h3
    rw [← hrep x]
    exact hK.sum_mem (fun i _ => hnn i) (hone x) (fun i _ => hvK i)
  · rintro _ ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖τ x - p‖ ^ 2 = a * (((n : ℝ) + 1) * ∑ k, b.coord k x ^ 2 - 1) := by
      rw [← real_inner_self_eq_norm_sq]
      nth_rewrite 2 [hτrep x]
      rw [inner_sum]
      simp_rw [real_inner_smul_right, hinner x]
      have e : ∀ k, b.coord k x * (a * (((n : ℝ) + 1) * b.coord k x - 1)) =
          a * ((n : ℝ) + 1) * b.coord k x ^ 2 - a * b.coord k x := by intro k; ring
      simp_rw [e]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hone]
      ring
    have hbd := LenstraRoundHelp.sumsq_bound n hn (fun k => b.coord k x) (hone x) (hcoordK x hx)
    have hR2 : (2 * n * Real.sqrt n * t) ^ 2 = 4 * (n : ℝ) ^ 2 * a := by
      rw [mul_pow, mul_pow, mul_pow, hsn2, ht2]; field_simp; ring
    have hX : ‖τ x - p‖ ^ 2 ≤ (2 * n * Real.sqrt n * t) ^ 2 := by
      rw [hnorm, hR2]
      have := mul_le_mul_of_nonneg_left hbd ha0.le
      nlinarith
    have hRpos : 0 < 2 * n * Real.sqrt n * t := by positivity
    nlinarith [norm_nonneg (τ x - p)]
  · have e : (n : ℝ) ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [e, mul_div_assoc, div_self ht0.ne', mul_one]
    exact le_of_eq (by ring)
