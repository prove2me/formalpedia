-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.no_large_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:42:42.190447+00:00
-- url     : https://prove2.me/submissions/f601bf9f-f8ba-441e-baae-3a1598dd24f9

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hE : ¬∃ i j, i ≠ j ∧ a / (4 * Fintype.card ι) ≤ |x i| ∧
      a / (4 * Fintype.card ι) ≤ |x j|)
    (hB : |∑ i, x i| < a / 2) (i : ι) : |x i| < a := by
  by_contra hc
  push_neg at hc
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn1 : (1:ℝ) ≤ n := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [hn]; exact_mod_cast this
  have hsmall : a / (4 * n) ≤ a := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hj : ∀ j ∈ Finset.univ.erase i, |x j| ≤ a / (4 * n) := by
    intro j hj
    by_contra h; push_neg at h
    exact hE ⟨i, j, (Finset.ne_of_mem_erase hj).symm, hsmall.trans hc, h.le⟩
  have hrest : |∑ j ∈ Finset.univ.erase i, x j| ≤ a / 4 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hj).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    have hc1 : ((Fintype.card ι - 1 : ℕ) : ℝ) ≤ n := by rw [hn]; exact_mod_cast Nat.sub_le _ _
    calc ((Fintype.card ι - 1 : ℕ) : ℝ) * (a / (4 * n)) ≤ n * (a / (4 * n)) :=
          mul_le_mul_of_nonneg_right hc1 (by positivity)
      _ = a / 4 := by field_simp
  have hsplit := Finset.add_sum_erase Finset.univ x (Finset.mem_univ i)
  have h1 : |x i| ≤ |∑ j, x j| + |∑ j ∈ Finset.univ.erase i, x j| := by
    rw [← hsplit]
    calc |x i| = |(x i + ∑ j ∈ Finset.univ.erase i, x j) - ∑ j ∈ Finset.univ.erase i, x j| := by ring_nf
      _ ≤ _ := abs_sub _ _
  linarith

