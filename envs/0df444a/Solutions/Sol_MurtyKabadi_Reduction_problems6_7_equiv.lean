-- Prove2me | solution 1 for MurtyKabadi.Reduction.problems6_7_equiv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:06:28.555765+00:00
-- url     : https://prove2.me/submissions/1af321f1-f9a9-4aeb-b834-414363594a93

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

theorem aux_p67_quad (A B ρ X : ℝ) (hA : 0 < A) (hρ : B ^ 2 ≤ 4 * A * ρ) :
    B * X - ρ ≤ A * X ^ 2 := by
  nlinarith [sq_nonneg (2 * A * X - B)]

/-- Per-coordinate estimate. -/
theorem aux_p67_coord (y s d a δ ρ : ℝ) (hy : 0 ≤ y) (hs : 0 ≤ s) (hd : 0 ≤ d) (hda : d ≤ a)
    (hδa : 0 < δ - 2 * a) (hρ : (2 * a + d) ^ 2 ≤ 4 * (δ - 2 * a) * ρ) :
    d * |y - (if s < y then 1 else 0)| - ρ ≤
      δ * (y + s - 1) ^ 2 + y * s + 2 * a * (y * (1 - y)) := by
  have ha : 0 ≤ a := le_trans hd hda
  have hδ0 : 0 ≤ δ := by linarith
  have hρ0 : 0 ≤ ρ := by
    by_contra h
    push Not at h
    have : 4 * (δ - 2 * a) * ρ < 0 := by
      have := mul_pos (by norm_num : (0:ℝ) < 4) hδa
      nlinarith
    nlinarith [sq_nonneg (2 * a + d)]
  have hq : ∀ X : ℝ, (2 * a + d) * X - ρ ≤ (δ - 2 * a) * X ^ 2 :=
    fun X => aux_p67_quad _ _ _ X hδa hρ
  split_ifs with h
  · -- s < y
    have he : |y - 1| ≤ s + |y + s - 1| := by
      have : y - 1 = (y + s - 1) - s := by ring
      rw [this]
      calc |(y + s - 1) - s| ≤ |y + s - 1| + |s| := abs_sub _ _
        _ = s + |y + s - 1| := by rw [abs_of_nonneg hs]; ring
    have hQ : (δ - 2 * a) * (y + s - 1) ^ 2 + a * s - 2 * a * |y + s - 1|
        ≤ δ * (y + s - 1) ^ 2 + y * s + 2 * a * (y * (1 - y)) := by
      have h1 : 0 ≤ a * s * (y - s) := mul_nonneg (mul_nonneg ha hs) (by linarith)
      rcases le_or_gt 0 (y + s - 1) with hu | hu
      · rw [abs_of_nonneg hu]
        have h2 : 0 ≤ a * (y + s - 1) * s := mul_nonneg (mul_nonneg ha hu) hs
        nlinarith [mul_nonneg hy hs]
      · rw [abs_of_neg hu]
        have h2 : 0 ≤ a * (-(y + s - 1)) * (2 * y - s) :=
          mul_nonneg (mul_nonneg ha (by linarith)) (by linarith)
        nlinarith [mul_nonneg hy hs, mul_nonneg ha (sq_nonneg (y + s - 1)),
          mul_nonneg ha (by linarith : (0:ℝ) ≤ -(y + s - 1))]
    have h3 := hq |y + s - 1|
    have h4 : d * |y - 1| ≤ d * (s + |y + s - 1|) := mul_le_mul_of_nonneg_left he hd
    have h5 : d * s ≤ a * s := mul_le_mul_of_nonneg_right hda hs
    rw [sq_abs] at h3
    nlinarith
  · -- y ≤ s
    push Not at h
    rw [sub_zero, abs_of_nonneg hy]
    have h1 : 0 ≤ a * y * (s - y) := mul_nonneg (mul_nonneg ha hy) (by linarith)
    have h5 : d * y ≤ a * y := mul_le_mul_of_nonneg_right hda hy
    rcases le_or_gt (y + s - 1) 0 with hu | hu
    · have h2 : 0 ≤ a * y * (-(y + s - 1)) := mul_nonneg (mul_nonneg ha hy) (by linarith)
      nlinarith [mul_nonneg hy hs, mul_nonneg hδ0 (sq_nonneg (y + s - 1))]
    · have h2 : 0 ≤ a * (y + s - 1) * (s - y) := mul_nonneg (mul_nonneg ha hu.le) (by linarith)
      have h3 := hq (y + s - 1)
      nlinarith [mul_nonneg hy hs, mul_nonneg ha hu.le, mul_nonneg ha (sq_nonneg (y + s - 1)),
        mul_nonneg hd hu.le]

theorem aux_p67_forward {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (hδ : 0 < δ)
    (y s : Fin n → ℝ) (hy : 0 ≤ y) (hs : 0 ≤ s) (hf : f1 d d0 δ y s ≤ 0) :
    f2 d d0 δ y s ≤ 0 := by
  have hδr : (0:ℝ) < δ := by exact_mod_cast hδ
  have hy' : ∀ j, 0 ≤ y j := fun j => hy j
  have hs' : ∀ j, 0 ≤ s j := fun j => hs j
  unfold f1 at hf
  have h1 : 0 ≤ (∑ j, (d j : ℝ) * y j - d0) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ ∑ j, (y j + s j - 1) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have h3 : 0 ≤ ∑ j, y j * s j := Finset.sum_nonneg (fun j _ => mul_nonneg (hy' j) (hs' j))
  have h2' : ∑ j, (y j + s j - 1) ^ 2 = 0 := by
    have : (δ:ℝ) * ∑ j, (y j + s j - 1) ^ 2 ≤ 0 := by linarith
    have h0 : ∑ j, (y j + s j - 1) ^ 2 ≤ 0 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hδr hc]
    linarith
  have h3' : ∑ j, y j * s j = 0 := by nlinarith [mul_nonneg hδr.le h2]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)] at h2'
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hy' j) (hs' j))] at h3'
  have h4 : ∑ j, (d j : ℝ) * y j * (1 - y j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have ha := h2' j hj
    have hb := h3' j hj
    have hc : y j + s j - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp ha
    have : 1 - y j = s j := by linarith
    rw [mul_assoc, this, hb, mul_zero]
  unfold f2 f1
  rw [h4]
  linarith

theorem aux_p67_backward {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ)
    (y s : Fin n → ℝ) (hy : 0 ≤ y) (hs : 0 ≤ s) (hf : f2 d d0 δ y s ≤ 0) :
    ∃ p ∈ P n, f1 d d0 δ p.1 p.2 ≤ 0 := by
  have hy' : ∀ j, 0 ≤ y j := fun j => hy j
  have hs' : ∀ j, 0 ≤ s j := fun j => hs j
  -- witness from a 0/1 vector
  have key : ∀ z : Fin n → ℝ, (∀ j, z j = 0 ∨ z j = 1) → ∑ j, (d j : ℝ) * z j = d0 →
      ∃ p ∈ P n, f1 d d0 δ p.1 p.2 ≤ 0 := by
    intro z hz hsum
    refine ⟨(z, fun j => 1 - z j), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro j; rcases hz j with h | h <;> simp [h]
    · intro j; rcases hz j with h | h <;> simp [h]
    · simp
    · unfold f1
      have e1 : ∑ j, (z j + (1 - z j) - 1) ^ 2 = 0 := by simp
      have e2 : ∑ j, z j * (1 - z j) = 0 := by
        apply Finset.sum_eq_zero; intro j _; rcases hz j with h | h <;> simp [h]
      simp only at e1 e2 ⊢
      rw [hsum, e1, e2]; simp
  by_cases hM : d0 * ∑ j, d j = 1
  · have h1 := mul_eq_one.mp hM
    apply key (fun _ => 1) (fun _ => Or.inr rfl)
    simp only [mul_one]
    have : ((∑ j, d j : ℕ) : ℝ) = (d0 : ℝ) := by rw [h1.1, h1.2]
    push_cast at this
    exact this
  · obtain ⟨Mr, hMr⟩ : ∃ Mr : ℝ, Mr = (d0 : ℝ) * ∑ j, (d j : ℝ) := ⟨_, rfl⟩
    have hMnat : 3 * (d0 * ∑ j, d j) ^ 2 + 2 * (d0 * ∑ j, d j) < δ := by
      rcases Nat.lt_or_ge (d0 * ∑ j, d j) 2 with h2 | h2
      · have h0 : d0 * ∑ j, d j = 0 := by omega
        rw [h0] at hδ ⊢; simpa using hδ
      · have hn : 1 ≤ n := by
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn; simp at h2
          · exact hn
        have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
        have : 4 * (d0 * ∑ j, d j) ^ 2 ≤ 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 :=
          Nat.le_mul_of_pos_right _ hn3
        nlinarith
    have hMδ : 3 * Mr ^ 2 + 2 * Mr < δ := by
      rw [hMr]; exact_mod_cast hMnat
    have hdj : ∀ j, (d j : ℝ) ≤ ∑ k, (d k : ℝ) := fun j =>
      Finset.single_le_sum (fun k _ => Nat.cast_nonneg (d k)) (Finset.mem_univ j)
    have hd0r : (1:ℝ) ≤ d0 := by exact_mod_cast hd0
    have hMr0 : 0 ≤ Mr := by rw [hMr]; positivity
    have hδM : 0 < (δ:ℝ) - 2 * Mr := by nlinarith
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 9 * Mr / (4 * ((δ:ℝ) - 2 * Mr)) := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) (by linarith)
    have htM : 4 * ((δ:ℝ) - 2 * Mr) * t = 9 * Mr := by
      rw [ht]; field_simp
    have htM' : t * Mr < 3 / 4 := by
      rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
    let z : Fin n → ℝ := fun j => if s j < y j then 1 else 0
    have hcoord : ∀ j, (d j : ℝ) * |y j - z j| - t * (d0 * d j) ≤
        δ * (y j + s j - 1) ^ 2 + y j * s j + 2 * ((d0:ℝ) * d j) * (y j * (1 - y j)) := by
      intro j
      have hdj0 : (0:ℝ) ≤ d j := Nat.cast_nonneg _
      have haM : (d0:ℝ) * d j ≤ Mr := by
        rw [hMr]; exact mul_le_mul_of_nonneg_left (hdj j) (by positivity)
      have hdle : (d j : ℝ) ≤ d0 * d j := by nlinarith
      apply aux_p67_coord (y j) (s j) (d j) ((d0:ℝ) * d j) δ (t * (d0 * d j)) (hy' j) (hs' j)
        hdj0 hdle
      · linarith
      · have e1 : 4 * ((δ:ℝ) - 2 * Mr) * t * (d0 * d j) ≤
            4 * ((δ:ℝ) - 2 * (d0 * d j)) * (t * (d0 * d j)) := by
          have : 0 ≤ t * (d0 * d j) := by positivity
          nlinarith
        rw [htM] at e1
        nlinarith
    have hsumQ : ∑ j, ((d j : ℝ) * |y j - z j| - t * (d0 * d j)) ≤
        ∑ j, (δ * (y j + s j - 1) ^ 2 + y j * s j + 2 * ((d0:ℝ) * d j) * (y j * (1 - y j))) :=
      Finset.sum_le_sum (fun j _ => hcoord j)
    have hQeq : ∑ j, (δ * (y j + s j - 1) ^ 2 + y j * s j + 2 * ((d0:ℝ) * d j) * (y j * (1 - y j)))
        = (δ:ℝ) * ∑ j, (y j + s j - 1) ^ 2 + ∑ j, y j * s j
          + 2 * (d0:ℝ) * ∑ j, (d j : ℝ) * y j * (1 - y j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    have hLeq : ∑ j, ((d j : ℝ) * |y j - z j| - t * (d0 * d j))
        = ∑ j, (d j : ℝ) * |y j - z j| - t * Mr := by
      rw [Finset.sum_sub_distrib, hMr, Finset.mul_sum, Finset.mul_sum]
    have hf2eq : f2 d d0 δ y s = (∑ j, (d j : ℝ) * y j - d0) ^ 2 +
        ((δ:ℝ) * ∑ j, (y j + s j - 1) ^ 2 + ∑ j, y j * s j
          + 2 * (d0:ℝ) * ∑ j, (d j : ℝ) * y j * (1 - y j)) := by
      unfold f2 f1; ring
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑ j, (d j : ℝ) * |y j - z j| := ⟨_, rfl⟩
    have hmain : (∑ j, (d j : ℝ) * y j - d0) ^ 2 + E - t * Mr ≤ 0 := by
      rw [hE]; linarith
    have hW : |∑ j, (d j : ℝ) * (y j - z j)| ≤ E := by
      calc |∑ j, (d j : ℝ) * (y j - z j)| ≤ ∑ j, |(d j : ℝ) * (y j - z j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = E := by
          rw [hE]; apply Finset.sum_congr rfl; intro j _; rw [abs_mul, Nat.abs_cast]
    have hsplit : ∑ j, (d j : ℝ) * z j - d0
        = (∑ j, (d j : ℝ) * y j - d0) - ∑ j, (d j : ℝ) * (y j - z j) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    have hround : |∑ j, (d j : ℝ) * z j - d0| ≤ |∑ j, (d j : ℝ) * y j - d0| + E := by
      rw [hsplit]
      calc |(∑ j, (d j : ℝ) * y j - d0) - ∑ j, (d j : ℝ) * (y j - z j)|
          ≤ |∑ j, (d j : ℝ) * y j - d0| + |∑ j, (d j : ℝ) * (y j - z j)| := abs_sub _ _
        _ ≤ |∑ j, (d j : ℝ) * y j - d0| + E := by linarith
    have hA : |∑ j, (d j : ℝ) * y j - d0| - (∑ j, (d j : ℝ) * y j - d0) ^ 2 ≤ 1 / 4 := by
      nlinarith [sq_abs (∑ j, (d j : ℝ) * y j - d0),
        sq_nonneg (|∑ j, (d j : ℝ) * y j - d0| - 1 / 2)]
    have hlt : |∑ j, (d j : ℝ) * z j - d0| < 1 := by linarith
    have hzcast : ((∑ j, d j * (if s j < y j then 1 else 0) : ℕ) : ℝ) = ∑ j, (d j : ℝ) * z j := by
      push_cast
      apply Finset.sum_congr rfl; intro j _
      simp only [z]
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (N:ℝ) = ∑ j, (d j : ℝ) * z j := ⟨_, hzcast⟩
    rw [← hN] at hlt
    have hNd : N = d0 := by
      have h1 : |((N:ℤ) - (d0:ℤ) : ℤ)| < 1 := by
        have : |(((N:ℤ) - (d0:ℤ) : ℤ) : ℝ)| < 1 := by push_cast; exact hlt
        exact_mod_cast this
      have := Int.abs_lt_one_iff.mp h1
      omega
    apply key z (fun j => by simp only [z]; split_ifs <;> simp)
    rw [← hN, hNd]

end MurtyKabadi.Reduction

open MurtyKabadi.Reduction

theorem solution {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ) :
    (∃ p ∈ P n, f1 d d0 δ p.1 p.2 ≤ 0) ↔ ∃ p ∈ P n, f2 d d0 δ p.1 p.2 ≤ 0 := by
  constructor
  · rintro ⟨p, hp, hf⟩
    obtain ⟨h1, h2, _⟩ := hp
    exact ⟨p, ⟨h1, h2, by assumption⟩, aux_p67_forward d d0 δ
      (lt_of_le_of_lt (Nat.zero_le _) hδ) p.1 p.2 h1 h2 hf⟩
  · rintro ⟨p, hp, hf⟩
    obtain ⟨h1, h2, _⟩ := hp
    exact aux_p67_backward d d0 δ hd0 hδ p.1 p.2 h1 h2 hf
