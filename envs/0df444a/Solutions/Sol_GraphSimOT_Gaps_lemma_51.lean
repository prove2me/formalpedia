-- Prove2me | solution 1 for GraphSimOT.Gaps.lemma_51
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:08:21.587618+00:00
-- url     : https://prove2.me/submissions/8a84bd82-43b0-40dc-a51d-142479c46f95

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Spectral

open Matrix GraphSimOT.Gaps

namespace Lemma51Aux

lemma gammaQ_bddAbove {n : ℕ} (hn : n ≠ 0) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n)) (A' B' : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove {r : ℝ | ∃ f g : Fin n → Fin n → ℝ, normQ Q f = 1 ∧ normQ Q g = 1 ∧
      r = |(1 / (n : ℝ) ^ 2) *
        ∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l|} := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  rw [mem_doublyStochastic_iff_sum] at hQ
  rcases hQ with ⟨hQnn, hQrow, -⟩
  let i0 : Fin n := ⟨0, hn0⟩
  have huniv_ne : (Finset.univ : Finset ((Fin n × Fin n) × (Fin n × Fin n))).Nonempty :=
    ⟨((i0, i0), (i0, i0)), Finset.mem_univ _⟩
  let M0 : ℝ := Finset.univ.sup' huniv_ne (fun p => |A' p.1.1 p.2.1 - B' p.1.2 p.2.2|)
  have hM0_nn : 0 ≤ M0 :=
    (abs_nonneg _).trans (Finset.le_sup' (fun p : (Fin n × Fin n) × (Fin n × Fin n) =>
      |A' p.1.1 p.2.1 - B' p.1.2 p.2.2|) (Finset.mem_univ ((i0, i0), (i0, i0))))
  have hentry : ∀ i j k l : Fin n, |A' i k - B' j l| ≤ M0 := fun i j k l =>
    Finset.le_sup' (fun p : (Fin n × Fin n) × (Fin n × Fin n) =>
      |A' p.1.1 p.2.1 - B' p.1.2 p.2.2|) (Finset.mem_univ ((i, j), (k, l)))
  refine ⟨M0, ?_⟩
  rintro r ⟨f, g, hf, hg, rfl⟩
  have hbound_l1 : ∀ h : Fin n → Fin n → ℝ, normQ Q h = 1 →
      ∑ i : Fin n, ∑ j : Fin n, Q i j * |h i j| ≤ n := by
    intro h hh
    have hinner : innerQ Q h h = 1 := by
      have hnn : 0 ≤ innerQ Q h h := by
        unfold innerQ
        apply mul_nonneg (by positivity)
        apply Finset.sum_nonneg; intro i _
        apply Finset.sum_nonneg; intro j _
        have : Q i j * h i j * h i j = Q i j * (h i j ^ 2) := by ring
        rw [this]
        exact mul_nonneg (hQnn i j) (sq_nonneg _)
      have hsq : Real.sqrt (innerQ Q h h) ^ 2 = 1 ^ 2 := by rw [← normQ, hh]
      rw [Real.sq_sqrt hnn] at hsq
      linarith
    have hsum_sq : ∑ i : Fin n, ∑ j : Fin n, Q i j * h i j ^ 2 = n := by
      unfold innerQ at hinner
      have : ∑ i : Fin n, ∑ j : Fin n, Q i j * h i j * h i j =
          ∑ i : Fin n, ∑ j : Fin n, Q i j * h i j ^ 2 := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _; ring
      rw [this, one_div_mul_eq_div, div_eq_iff hnR.ne'] at hinner
      linarith
    have hsum_Q : ∑ i : Fin n, ∑ j : Fin n, Q i j = n := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, Q i j = ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_congr rfl fun i _ => hQrow i
        _ = n := by simp
    have hpt : ∀ i j : Fin n, 2 * (Q i j * |h i j|) ≤ Q i j + Q i j * h i j ^ 2 := by
      intro i j
      have hsq : 0 ≤ (|h i j| - 1) ^ 2 := sq_nonneg _
      have h1 : 2 * |h i j| ≤ 1 + h i j ^ 2 := by nlinarith [sq_abs (h i j)]
      have h2 := mul_le_mul_of_nonneg_left h1 (hQnn i j)
      linarith
    have hsum2 : 2 * ∑ i : Fin n, ∑ j : Fin n, Q i j * |h i j| ≤ 2 * (n : ℝ) := by
      calc
        2 * ∑ i : Fin n, ∑ j : Fin n, Q i j * |h i j|
            = ∑ i : Fin n, ∑ j : Fin n, 2 * (Q i j * |h i j|) := by
                simp_rw [Finset.mul_sum]
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, (Q i j + Q i j * h i j ^ 2) := by
              apply Finset.sum_le_sum; intro i _
              apply Finset.sum_le_sum; intro j _; exact hpt i j
        _ = (∑ i : Fin n, ∑ j : Fin n, Q i j) +
            (∑ i : Fin n, ∑ j : Fin n, Q i j * h i j ^ 2) := by
              simp_rw [Finset.sum_add_distrib]
        _ = 2 * (n : ℝ) := by linarith
    linarith
  have hf1 := hbound_l1 f hf
  have hg1 := hbound_l1 g hg
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hn2)]
  have hterm_le : ∀ i j k l : Fin n,
      |f i j * Q i j * Q k l * (A' i k - B' j l) * g k l| ≤
        (Q i j * |f i j|) * (Q k l * |g k l|) * M0 := by
    intro i j k l
    have hrew : |f i j * Q i j * Q k l * (A' i k - B' j l) * g k l| =
        (Q i j * |f i j|) * (Q k l * |g k l|) * |A' i k - B' j l| := by
      calc
        |f i j * Q i j * Q k l * (A' i k - B' j l) * g k l|
            = |Q i j| * |Q k l| * |f i j| * |g k l| * |A' i k - B' j l| := by
                rw [abs_mul, abs_mul, abs_mul, abs_mul]; ring
        _ = (Q i j * |f i j|) * (Q k l * |g k l|) * |A' i k - B' j l| := by
                rw [abs_of_nonneg (hQnn i j), abs_of_nonneg (hQnn k l)]; ring
    rw [hrew]
    exact mul_le_mul_of_nonneg_left (hentry i j k l)
      (mul_nonneg (mul_nonneg (hQnn i j) (abs_nonneg _)) (mul_nonneg (hQnn k l) (abs_nonneg _)))
  calc
    (1 / (n : ℝ) ^ 2) * |∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l|
        ≤ (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, ∑ k, ∑ l,
            |f i j * Q i j * Q k l * (A' i k - B' j l) * g k l| := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, ∑ k, ∑ l,
          (Q i j * |f i j|) * (Q k l * |g k l|) * M0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          apply Finset.sum_le_sum; intro k _
          apply Finset.sum_le_sum; intro l _; exact hterm_le i j k l
    _ = (1 / (n : ℝ) ^ 2) * ((∑ i, ∑ j, Q i j * |f i j|) * (∑ k, ∑ l, Q k l * |g k l|) * M0) := by
          congr 1
          calc
            (∑ i, ∑ j, ∑ k, ∑ l, (Q i j * |f i j|) * (Q k l * |g k l|) * M0)
                = ∑ i, ∑ j, (Q i j * |f i j|) * (∑ k, ∑ l, (Q k l * |g k l|) * M0) := by
                    apply Finset.sum_congr rfl; intro i _
                    apply Finset.sum_congr rfl; intro j _
                    simp only [Finset.mul_sum, mul_assoc]
            _ = (∑ i, ∑ j, Q i j * |f i j|) * (∑ k, ∑ l, Q k l * |g k l|) * M0 := by
                  have hinner : (∑ k, ∑ l, (Q k l * |g k l|) * M0) =
                      (∑ k, ∑ l, Q k l * |g k l|) * M0 := by
                    simp only [Finset.sum_mul]
                  simp_rw [hinner]
                  simp only [Finset.sum_mul, mul_assoc]
    _ ≤ (1 / (n : ℝ) ^ 2) * ((n : ℝ) * (n : ℝ) * M0) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hM0_nn
          exact mul_le_mul hf1 hg1 (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
            mul_nonneg (hQnn k l) (abs_nonneg _)) hnR.le
    _ = M0 := by
          have hn2' : (n : ℝ) ^ 2 ≠ 0 := hn2.ne'
          calc
            (1 / (n : ℝ) ^ 2) * ((n : ℝ) * (n : ℝ) * M0)
                = ((1 / (n : ℝ) ^ 2) * (n : ℝ) ^ 2) * M0 := by ring
            _ = M0 := by rw [one_div_mul_cancel hn2', one_mul]

end Lemma51Aux

theorem solution {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (A' B' : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, Q i j * ((A' *ᵥ y) i - (Qᵀ *ᵥ (A' *ᵥ y)) j) ^ 2
      ≤ gammaQ Q A' B' ^ 2 * ∑ i, y i ^ 2 := by
  by_cases hn : n = 0
  · subst hn; simp
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hQ' := hQ
  rw [mem_doublyStochastic_iff_sum] at hQ'
  rcases hQ' with ⟨hQnn, hQrow, hQcol⟩
  set x : Fin n → ℝ := A' *ᵥ y
  set r : Fin n → ℝ := B' *ᵥ (Qᵀ *ᵥ y)
  set F : Fin n → Fin n → ℝ := fun i j => ∑ k : Fin n, ∑ l : Fin n, Q k l * (A' i k - B' j l) * y k
  have hF_eq : ∀ i j : Fin n, F i j = x i - r j := by
    intro i j
    simp only [F, sub_mul, mul_sub, Finset.sum_sub_distrib]
    have ht1 : ∑ k : Fin n, ∑ l : Fin n, Q k l * A' i k * y k = x i := by
      calc
        ∑ k : Fin n, ∑ l : Fin n, Q k l * A' i k * y k
            = ∑ k : Fin n, A' i k * y k * (∑ l : Fin n, Q k l) := by
                apply Finset.sum_congr rfl; intro k _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro l _; ring
        _ = ∑ k : Fin n, A' i k * y k := by
                apply Finset.sum_congr rfl; intro k _
                rw [hQrow k, mul_one]
        _ = x i := by simp only [x, Matrix.mulVec, dotProduct]
    have ht2 : ∑ k : Fin n, ∑ l : Fin n, Q k l * B' j l * y k = r j := by
      calc
        ∑ k : Fin n, ∑ l : Fin n, Q k l * B' j l * y k
            = ∑ l : Fin n, B' j l * (∑ k : Fin n, Q k l * y k) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro l _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro k _; ring
        _ = r j := by simp only [r, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [ht1, ht2]
  set m : Fin n → ℝ := fun j => ∑ i' : Fin n, Q i' j * F i' j
  have hdiff : ∀ i j : Fin n, x i - (Qᵀ *ᵥ x) j = F i j - m j := by
    intro i j
    have hQtx : (Qᵀ *ᵥ x) j = r j + m j := by
      calc
        (Qᵀ *ᵥ x) j = ∑ i' : Fin n, Q i' j * x i' := by
            simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
        _ = ∑ i' : Fin n, Q i' j * (F i' j + r j) := by
            apply Finset.sum_congr rfl; intro i' _
            rw [hF_eq i' j]; ring
        _ = m j + r j * (∑ i' : Fin n, Q i' j) := by
            simp only [m, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
            ring
        _ = r j + m j := by rw [hQcol j]; ring
    rw [hQtx, hF_eq i j]; ring
  set S2 : ℝ := ∑ i : Fin n, ∑ j : Fin n, Q i j * F i j ^ 2
  set Y2 : ℝ := ∑ k : Fin n, y k ^ 2
  have hvar : ∑ i : Fin n, ∑ j : Fin n, Q i j * (x i - (Qᵀ *ᵥ x) j) ^ 2 ≤ S2 := by
    simp_rw [hdiff]
    have hexp : ∑ i : Fin n, ∑ j : Fin n, Q i j * (F i j - m j) ^ 2 =
        S2 - ∑ j : Fin n, m j ^ 2 := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, Q i j * (F i j - m j) ^ 2
            = ∑ j : Fin n, ∑ i : Fin n,
                (Q i j * F i j ^ 2 - 2 * m j * (Q i j * F i j) + m j ^ 2 * Q i j) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro j _
              apply Finset.sum_congr rfl; intro i _; ring
        _ = (∑ j : Fin n, ∑ i : Fin n, Q i j * F i j ^ 2) -
            ∑ j : Fin n, (2 * m j * (∑ i : Fin n, Q i j * F i j) -
              m j ^ 2 * (∑ i : Fin n, Q i j)) := by
              simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
              ring_nf
        _ = S2 - ∑ j : Fin n, m j ^ 2 := by
              rw [Finset.sum_comm]
              congr 1
              apply Finset.sum_congr rfl; intro j _
              rw [hQcol j]; simp only [m]; ring
    rw [hexp]
    have hmnn : 0 ≤ ∑ j : Fin n, m j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  suffices hS2 : (1 / (n : ℝ) ^ 2) * S2 ≤ gammaQ Q A' B' ^ 2 * Y2 by
    exact (mul_le_mul_of_nonneg_left hvar (by positivity)).trans hS2
  have hS2_nn : 0 ≤ S2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hQnn i j) (sq_nonneg _)
  have hY2_nn : 0 ≤ Y2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases hS2_nn.eq_or_lt with hS0 | hS_pos
  · rw [← hS0, mul_zero]; positivity
  rcases hY2_nn.eq_or_lt with hY0 | hY_pos
  · have hy0 : ∀ k : Fin n, y k = 0 := by
      intro k
      have hsq0 : y k ^ 2 ≤ 0 := by
        rw [hY0]
        exact Finset.single_le_sum (fun i _ => sq_nonneg (y i)) (Finset.mem_univ k)
      exact sq_eq_zero_iff.mp (le_antisymm hsq0 (sq_nonneg _))
    have hF0 : ∀ i j : Fin n, F i j = 0 := by
      intro i j; simp [F, hy0]
    have : S2 = 0 := by simp [S2, hF0]
    linarith
  let f : Fin n → Fin n → ℝ := fun i j => Real.sqrt ((n : ℝ) / S2) * F i j
  let g : Fin n → Fin n → ℝ := fun k _l => Real.sqrt ((n : ℝ) / Y2) * y k
  have hf_norm : normQ Q f = 1 := by
    unfold normQ innerQ
    have hsq : Real.sqrt ((n : ℝ) / S2) ^ 2 = (n : ℝ) / S2 :=
      Real.sq_sqrt (div_nonneg hnR.le hS_pos.le)
    have hsum : (∑ i : Fin n, ∑ j : Fin n, Q i j * f i j * f i j) =
        ((n : ℝ) / S2) * S2 := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, Q i j * f i j * f i j
            = ∑ i : Fin n, ∑ j : Fin n, Real.sqrt ((n : ℝ) / S2) ^ 2 * (Q i j * F i j ^ 2) := by
                apply Finset.sum_congr rfl; intro i _
                apply Finset.sum_congr rfl; intro j _
                simp only [f]; ring
        _ = ((n : ℝ) / S2) * S2 := by
                simp only [hsq, S2, Finset.mul_sum]
    rw [hsum, div_mul_cancel₀ _ hS_pos.ne', one_div_mul_cancel hnR.ne', Real.sqrt_one]
  have hg_norm : normQ Q g = 1 := by
    unfold normQ innerQ
    have hsq : Real.sqrt ((n : ℝ) / Y2) ^ 2 = (n : ℝ) / Y2 :=
      Real.sq_sqrt (div_nonneg hnR.le hY_pos.le)
    have hsum : (∑ k : Fin n, ∑ l : Fin n, Q k l * g k l * g k l) =
        ((n : ℝ) / Y2) * Y2 := by
      calc
        ∑ k : Fin n, ∑ l : Fin n, Q k l * g k l * g k l
            = ∑ k : Fin n, Real.sqrt ((n : ℝ) / Y2) ^ 2 * y k ^ 2 * (∑ l : Fin n, Q k l) := by
                apply Finset.sum_congr rfl; intro k _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro l _
                simp only [g]; ring
        _ = ∑ k : Fin n, ((n : ℝ) / Y2) * y k ^ 2 := by
                apply Finset.sum_congr rfl; intro k _
                rw [hQrow k, mul_one, hsq]
        _ = ((n : ℝ) / Y2) * Y2 := by
                simp only [Y2, Finset.mul_sum]
    rw [hsum, div_mul_cancel₀ _ hY_pos.ne', one_div_mul_cancel hnR.ne', Real.sqrt_one]
  have hbilin : (1 / (n : ℝ) ^ 2) *
      ∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l =
      Real.sqrt S2 / ((n : ℝ) * Real.sqrt Y2) := by
    have hsum : (∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l) =
        Real.sqrt ((n : ℝ) / S2) * Real.sqrt ((n : ℝ) / Y2) * S2 := by
      calc
        _ = ∑ i, ∑ j, (Real.sqrt ((n : ℝ) / S2) * Real.sqrt ((n : ℝ) / Y2)) *
              (Q i j * F i j * (∑ k, ∑ l, Q k l * (A' i k - B' j l) * y k)) := by
              apply Finset.sum_congr rfl; intro i _
              apply Finset.sum_congr rfl; intro j _
              simp only [Finset.mul_sum, f, g]
              apply Finset.sum_congr rfl; intro k _
              apply Finset.sum_congr rfl; intro l _; ring
        _ = ∑ i, ∑ j, (Real.sqrt ((n : ℝ) / S2) * Real.sqrt ((n : ℝ) / Y2)) * (Q i j * F i j ^ 2) := by
              apply Finset.sum_congr rfl; intro i _
              apply Finset.sum_congr rfl; intro j _
              congr 1
              change Q i j * F i j * F i j = Q i j * F i j ^ 2
              ring
        _ = Real.sqrt ((n : ℝ) / S2) * Real.sqrt ((n : ℝ) / Y2) * S2 := by
              simp only [S2, Finset.mul_sum]
    rw [hsum, Real.sqrt_div hnR.le, Real.sqrt_div hnR.le]
    have hsS : Real.sqrt S2 ≠ 0 := (Real.sqrt_pos.mpr hS_pos).ne'
    have hsY : Real.sqrt Y2 ≠ 0 := (Real.sqrt_pos.mpr hY_pos).ne'
    have hnsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hnR.le
    have hSsq : Real.sqrt S2 * Real.sqrt S2 = S2 := Real.mul_self_sqrt hS_pos.le
    field_simp
    nlinarith
  have hval_le : Real.sqrt S2 / ((n : ℝ) * Real.sqrt Y2) ≤ gammaQ Q A' B' := by
    unfold gammaQ
    apply le_csSup (Lemma51Aux.gammaQ_bddAbove hn Q hQ A' B')
    refine ⟨f, g, hf_norm, hg_norm, ?_⟩
    rw [hbilin, abs_of_nonneg (by positivity)]
  have hval_nn : 0 ≤ Real.sqrt S2 / ((n : ℝ) * Real.sqrt Y2) := by positivity
  have hsq_le : (Real.sqrt S2 / ((n : ℝ) * Real.sqrt Y2)) ^ 2 ≤ gammaQ Q A' B' ^ 2 :=
    pow_le_pow_left₀ hval_nn hval_le 2
  have hrew : (Real.sqrt S2 / ((n : ℝ) * Real.sqrt Y2)) ^ 2 = S2 / ((n : ℝ) ^ 2 * Y2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hS_pos.le, Real.sq_sqrt hY_pos.le]
  rw [hrew, div_le_iff₀ (mul_pos hn2 hY_pos)] at hsq_le
  calc
    (1 / (n : ℝ) ^ 2) * S2 = S2 / (n : ℝ) ^ 2 := one_div_mul_eq_div _ _
    _ ≤ gammaQ Q A' B' ^ 2 * Y2 := by
        rw [div_le_iff₀ hn2]
        linarith
