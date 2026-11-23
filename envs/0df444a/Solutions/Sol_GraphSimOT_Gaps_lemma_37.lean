-- Prove2me | solution 1 for GraphSimOT.Gaps.lemma_37
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:22:49.503352+00:00
-- url     : https://prove2.me/submissions/c0200159-447c-44f3-a4e4-1d402665cd05

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances
import Definitions.Def_GraphSimOT_Gaps_CutRounding

open Matrix GraphSimOT.Gaps

namespace Lemma37Aux

lemma sum_QF_le_cutNorm {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (S : Finset (Fin n × Fin n)) :
    |∑ a ∈ S, Q a.1 a.2 * (∑ k : Fin n, ∑ l : Fin n, Q k l * (adj G a.1 k - adj H a.2 l) * y k)|
      ≤ FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) := by
  classical
  let c : Fin n → ℝ := fun k => ∑ a ∈ S, ∑ l : Fin n, Bmat G H Q a (k, l)
  have hrew : (∑ a ∈ S, Q a.1 a.2 *
      (∑ k : Fin n, ∑ l : Fin n, Q k l * (adj G a.1 k - adj H a.2 l) * y k)) =
      ∑ k : Fin n, y k * c k := by
    calc
      _ = ∑ a ∈ S, ∑ k : Fin n, y k * (∑ l : Fin n, Bmat G H Q a (k, l)) := by
            apply Finset.sum_congr rfl; intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro l _
            unfold Bmat disc; ring
      _ = ∑ k : Fin n, y k * c k := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro k _
            simp only [c, Finset.mul_sum]
  rw [hrew]
  have hblock : ∀ K : Finset (Fin n),
      ∑ k ∈ K, c k =
        FriezeKannan.CutDecomp.blockSum (Bmat G H Q) S (K ×ˢ Finset.univ) := by
    intro K
    unfold FriezeKannan.CutDecomp.blockSum
    simp only [c]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_product]
  apply abs_le.mpr
  constructor
  · let Kneg : Finset (Fin n) := Finset.univ.filter (fun k => c k < 0)
    have h1 : -(∑ k : Fin n, y k * c k) ≤ -(∑ k ∈ Kneg, c k) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
          ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => c k < 0)]
      have hnonpos : ∑ k ∈ Finset.univ.filter (fun k => ¬ c k < 0), -(y k * c k) ≤ 0 := by
        apply Finset.sum_nonpos; intro k hk
        have hck : 0 ≤ c k := not_lt.mp (Finset.mem_filter.mp hk).2
        have hyk : 0 ≤ y k := (hy k).1
        nlinarith
      have hle_neg : ∑ k ∈ Kneg, -(y k * c k) ≤ ∑ k ∈ Kneg, -(c k) := by
        apply Finset.sum_le_sum; intro k hk
        have hck : c k < 0 := (Finset.mem_filter.mp hk).2
        have hyk : y k ≤ 1 := (hy k).2
        nlinarith
      linarith
    have h2 : -(∑ k ∈ Kneg, c k) ≤ FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) := by
      rw [hblock Kneg]
      refine (neg_le_abs _).trans ?_
      exact Finset.le_sup'
        (fun p : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) =>
          |FriezeKannan.CutDecomp.blockSum (Bmat G H Q) p.1 p.2|)
        (Finset.mem_univ (S, Kneg ×ˢ Finset.univ))
    linarith
  · let Kpos : Finset (Fin n) := Finset.univ.filter (fun k => 0 < c k)
    have h1 : ∑ k : Fin n, y k * c k ≤ ∑ k ∈ Kpos, c k := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => 0 < c k)]
      have hnonpos : ∑ k ∈ Finset.univ.filter (fun k => ¬ 0 < c k), y k * c k ≤ 0 := by
        apply Finset.sum_nonpos; intro k hk
        have hck : c k ≤ 0 := not_lt.mp (Finset.mem_filter.mp hk).2
        have hyk : 0 ≤ y k := (hy k).1
        nlinarith
      have hle_pos : ∑ k ∈ Kpos, y k * c k ≤ ∑ k ∈ Kpos, c k := by
        apply Finset.sum_le_sum; intro k hk
        have hck : 0 < c k := (Finset.mem_filter.mp hk).2
        have hyk : y k ≤ 1 := (hy k).2
        nlinarith
      linarith
    have h2 : ∑ k ∈ Kpos, c k ≤ FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) := by
      rw [hblock Kpos]
      refine (le_abs_self _).trans ?_
      exact Finset.le_sup'
        (fun p : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) =>
          |FriezeKannan.CutDecomp.blockSum (Bmat G H Q) p.1 p.2|)
        (Finset.mem_univ (S, Kpos ×ˢ Finset.univ))
    linarith

end Lemma37Aux

theorem solution {n : ℕ} (hn : 2 ≤ n) (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, Q i j * |(adj G *ᵥ y) i - (Qᵀ *ᵥ (adj G *ᵥ y)) j|
      ≤ 4 * zeta G H Q := by
  classical
  have hQ' := hQ
  rw [mem_doublyStochastic_iff_sum] at hQ'
  rcases hQ' with ⟨hQnn, hQrow, hQcol⟩
  set x : Fin n → ℝ := adj G *ᵥ y
  set r : Fin n → ℝ := adj H *ᵥ (Qᵀ *ᵥ y)
  set F : Fin n → Fin n → ℝ :=
    fun i j => ∑ k : Fin n, ∑ l : Fin n, Q k l * (adj G i k - adj H j l) * y k
  have hF_eq : ∀ i j : Fin n, F i j = x i - r j := by
    intro i j
    simp only [F, sub_mul, mul_sub, Finset.sum_sub_distrib]
    have ht1 : ∑ k : Fin n, ∑ l : Fin n, Q k l * adj G i k * y k = x i := by
      calc
        ∑ k : Fin n, ∑ l : Fin n, Q k l * adj G i k * y k
            = ∑ k : Fin n, adj G i k * y k * (∑ l : Fin n, Q k l) := by
                apply Finset.sum_congr rfl; intro k _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro l _; ring
        _ = ∑ k : Fin n, adj G i k * y k := by
                apply Finset.sum_congr rfl; intro k _
                rw [hQrow k, mul_one]
        _ = x i := by simp only [x, Matrix.mulVec, dotProduct]
    have ht2 : ∑ k : Fin n, ∑ l : Fin n, Q k l * adj H j l * y k = r j := by
      calc
        ∑ k : Fin n, ∑ l : Fin n, Q k l * adj H j l * y k
            = ∑ l : Fin n, adj H j l * (∑ k : Fin n, Q k l * y k) := by
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
  have htri_sum : ∑ i : Fin n, ∑ j : Fin n, Q i j * |x i - (Qᵀ *ᵥ x) j| ≤
      2 * ∑ i : Fin n, ∑ j : Fin n, Q i j * |F i j| := by
    have hpt : ∀ i j : Fin n, Q i j * |x i - (Qᵀ *ᵥ x) j| ≤
        Q i j * |F i j| + Q i j * (∑ i' : Fin n, Q i' j * |F i' j|) := by
      intro i j
      rw [hdiff i j, ← mul_add]
      apply mul_le_mul_of_nonneg_left _ (hQnn i j)
      have hm_abs : |m j| ≤ ∑ i' : Fin n, Q i' j * |F i' j| := by
        calc
          |m j| ≤ ∑ i' : Fin n, |Q i' j * F i' j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i' : Fin n, Q i' j * |F i' j| := by
                apply Finset.sum_congr rfl; intro i' _
                rw [abs_mul, abs_of_nonneg (hQnn i' j)]
      have htri := abs_sub (F i j) (m j)
      linarith
    calc
      ∑ i : Fin n, ∑ j : Fin n, Q i j * |x i - (Qᵀ *ᵥ x) j|
          ≤ ∑ i : Fin n, ∑ j : Fin n,
              (Q i j * |F i j| + Q i j * (∑ i' : Fin n, Q i' j * |F i' j|)) := by
            apply Finset.sum_le_sum; intro i _
            apply Finset.sum_le_sum; intro j _; exact hpt i j
      _ = (∑ i : Fin n, ∑ j : Fin n, Q i j * |F i j|) +
          (∑ j : Fin n, (∑ i : Fin n, Q i j) * (∑ i' : Fin n, Q i' j * |F i' j|)) := by
            simp_rw [Finset.sum_add_distrib]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.sum_mul]
      _ = 2 * ∑ i : Fin n, ∑ j : Fin n, Q i j * |F i j| := by
            have hsecond : (∑ j : Fin n, (∑ i : Fin n, Q i j) * (∑ i' : Fin n, Q i' j * |F i' j|)) =
                ∑ i' : Fin n, ∑ j : Fin n, Q i' j * |F i' j| := by
              calc
                _ = ∑ j : Fin n, ∑ i' : Fin n, Q i' j * |F i' j| := by
                      apply Finset.sum_congr rfl; intro j _
                      rw [hQcol j, one_mul]
                _ = _ := Finset.sum_comm
            rw [hsecond]; ring
  let Spos : Finset (Fin n × Fin n) := Finset.univ.filter (fun a => 0 < F a.1 a.2)
  let Sneg : Finset (Fin n × Fin n) := Finset.univ.filter (fun a => F a.1 a.2 < 0)
  have hF_abs_le : ∑ i : Fin n, ∑ j : Fin n, Q i j * |F i j| ≤
      2 * FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) := by
    rw [← Fintype.sum_prod_type (fun a : Fin n × Fin n => Q a.1 a.2 * |F a.1 a.2|)]
    have hsplit : (∑ a : Fin n × Fin n, Q a.1 a.2 * |F a.1 a.2|) =
        (∑ a ∈ Spos, Q a.1 a.2 * F a.1 a.2) +
        -(∑ a ∈ Sneg, Q a.1 a.2 * F a.1 a.2) := by
      dsimp only [Spos, Sneg]
      rw [← Finset.sum_neg_distrib, Finset.sum_filter, Finset.sum_filter,
          ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro a _
      rcases lt_trichotomy (F a.1 a.2) 0 with hlt | heq | hgt
      · have hnpos : ¬ 0 < F a.1 a.2 := not_lt.mpr hlt.le
        simp [hlt, hnpos, abs_of_neg hlt]
      · simp [heq]
      · have hnneg : ¬ F a.1 a.2 < 0 := not_lt.mpr hgt.le
        simp [hgt, hnneg, abs_of_pos hgt]
    rw [hsplit]
    have hbpos : ∑ a ∈ Spos, Q a.1 a.2 * F a.1 a.2 ≤
        FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) :=
      (le_abs_self _).trans (Lemma37Aux.sum_QF_le_cutNorm G H Q y hy Spos)
    have hbneg : -(∑ a ∈ Sneg, Q a.1 a.2 * F a.1 a.2) ≤
        FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) :=
      (neg_le_abs _).trans (Lemma37Aux.sum_QF_le_cutNorm G H Q y hy Sneg)
    linarith
  unfold zeta
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  calc
    (1 / (n : ℝ) ^ 2) * ∑ i : Fin n, ∑ j : Fin n, Q i j * |x i - (Qᵀ *ᵥ x) j|
        ≤ (1 / (n : ℝ) ^ 2) * (2 * ∑ i : Fin n, ∑ j : Fin n, Q i j * |F i j|) :=
          mul_le_mul_of_nonneg_left htri_sum (by positivity)
    _ ≤ (1 / (n : ℝ) ^ 2) * (2 * (2 * FriezeKannan.CutDecomp.cutNorm (Bmat G H Q))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
    _ = 4 * (FriezeKannan.CutDecomp.cutNorm (Bmat G H Q) / (n : ℝ) ^ 2) := by ring
