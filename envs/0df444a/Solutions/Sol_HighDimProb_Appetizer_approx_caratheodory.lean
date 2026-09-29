-- Prove2me | solution 1 for HighDimProb.Appetizer.approx_caratheodory
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:36:20.149612+00:00
-- url     : https://prove2.me/submissions/5ee53e68-49e5-4c29-8c12-397c1406b46f

import Mathlib

namespace HighDimProb.Appetizer

lemma ac_step {n : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (z : ι → EuclideanSpace ℝ (Fin n))
    (x v : EuclideanSpace ℝ (Fin n)) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hx : ∑ i, w i • z i = x) (hz : ∀ i, ‖z i - x‖ ≤ 1) :
    ∃ i, ‖v + (z i - x)‖ ^ 2 ≤ ‖v‖ ^ 2 + 1 := by
  by_contra hcon
  push Not at hcon
  have hmean : ∑ i, w i • (z i - x) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul, hx, sub_self]
  have h1 : ∀ i, w i * ‖v + (z i - x)‖ ^ 2 =
      w i * ‖v‖ ^ 2 + 2 * (w i * inner ℝ v (z i - x)) + w i * ‖z i - x‖ ^ 2 := by
    intro i; rw [norm_add_sq_real]; ring
  have h2 : ∑ i, w i * inner ℝ v (z i - x) = inner ℝ v (∑ i, w i • (z i - x)) := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_right]
  have h3 : ∑ i, w i * ‖z i - x‖ ^ 2 ≤ 1 := by
    calc ∑ i, w i * ‖z i - x‖ ^ 2 ≤ ∑ i, w i * 1 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (by have := hz i; have := norm_nonneg (z i - x); nlinarith)
            (hw0 i)
      _ = 1 := by simp [hw1]
  have hsum : ∑ i, w i * ‖v + (z i - x)‖ ^ 2 ≤ ‖v‖ ^ 2 + 1 := by
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, hw1, ← Finset.mul_sum, h2, hmean, inner_zero_right]
    linarith
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  have hlt : ∑ i, w i * (‖v‖ ^ 2 + 1) < ∑ i, w i * ‖v + (z i - x)‖ ^ 2 := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (hcon i).le (hw0 i)
    · exact ⟨i0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hcon i0) hi0⟩
  rw [← Finset.sum_mul, hw1, one_mul] at hlt
  linarith

theorem ac_main {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n)))
    (hTb : Bornology.IsBounded T) (hT : Metric.diam T ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ convexHull ℝ T)
    (k : ℕ) (hk : 0 < k) :
    ∃ x' : Fin k → EuclideanSpace ℝ (Fin n), (∀ j, x' j ∈ T) ∧
      ‖x - (k : ℝ)⁻¹ • ∑ j, x' j‖ ≤ 1 / Real.sqrt k := by
  obtain ⟨ι, hι, w, z, hw0, hw1, hzT, hxz⟩ := mem_convexHull_iff_exists_fintype.mp hx
  have hdist : ∀ i, ‖z i - x‖ ≤ 1 := by
    intro i
    have hb : Bornology.IsBounded (convexHull ℝ T) := isBounded_convexHull.mpr hTb
    have := Metric.dist_le_diam_of_mem hb (subset_convexHull ℝ T (hzT i)) hx
    rw [convexHull_diam] at this
    rw [← dist_eq_norm]; linarith
  have hind : ∀ m : ℕ, ∃ x' : Fin m → EuclideanSpace ℝ (Fin n), (∀ j, x' j ∈ T) ∧
      ‖∑ j, (x' j - x)‖ ^ 2 ≤ m := by
    intro m
    induction m with
    | zero => exact ⟨Fin.elim0, fun j => j.elim0, by simp⟩
    | succ m ih =>
      obtain ⟨x', hx'T, hx'⟩ := ih
      obtain ⟨i, hi⟩ := ac_step w z x (∑ j, (x' j - x)) hw0 hw1 hxz hdist
      refine ⟨Fin.cons (z i) x', fun j => ?_, ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa using hzT i
        · simpa using hx'T j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [add_comm]
        push_cast
        linarith
  obtain ⟨x', hx'T, hx'⟩ := hind k
  refine ⟨x', hx'T, ?_⟩
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have e : x - (k : ℝ)⁻¹ • ∑ j, x' j = -((k : ℝ)⁻¹ • ∑ j, (x' j - x)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hkpos.ne', one_smul]
    abel
  rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hkpos]
  have hs : ‖∑ j, (x' j - x)‖ ≤ Real.sqrt k := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hx'
  have hspos := Real.sqrt_pos.mpr hkpos
  calc (k:ℝ)⁻¹ * ‖∑ j, (x' j - x)‖ ≤ (k:ℝ)⁻¹ * Real.sqrt k :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hkpos.le)
    _ = 1 / Real.sqrt k := by
        rw [inv_mul_eq_div, div_eq_div_iff hkpos.ne' hspos.ne', one_mul,
          Real.mul_self_sqrt hkpos.le]

end HighDimProb.Appetizer

open HighDimProb.Appetizer

theorem solution {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n)))
    (hTb : Bornology.IsBounded T) (hT : Metric.diam T ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ convexHull ℝ T)
    (k : ℕ) (hk : 0 < k) :
    ∃ x' : Fin k → EuclideanSpace ℝ (Fin n), (∀ j, x' j ∈ T) ∧
      ‖x - (k : ℝ)⁻¹ • ∑ j, x' j‖ ≤ 1 / Real.sqrt k := by
  exact ac_main T hTb hT x hx k hk
