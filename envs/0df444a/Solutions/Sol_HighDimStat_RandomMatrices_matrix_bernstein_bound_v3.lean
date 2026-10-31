-- Prove2me | solution 1 for HighDimStat.RandomMatrices.matrix_bernstein_bound_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T04:17:44.217488+00:00
-- url     : https://prove2.me/submissions/26c71c4d-6650-4cb9-9bab-f788bb692307
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_matrixExpectation
import Definitions.Def_HighDimStat_RandomMatrices_matrixVariance
import Definitions.Def_HighDimStat_RandomMatrices_LoewnerLE
import Definitions.Def_HighDimStat_RandomMatrices_BernsteinConditionMatrix
import Definitions.Def_HighDimStat_RandomMatrices_opNorm
import Theorems.Thm_HighDimStat_RandomMatrices_matrix_bernstein_laplace_mgf_bound

open MeasureTheory ProbabilityTheory HighDimStat.RandomMatrices

lemma opNorm_nonneg_aux {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ opNorm M := by
  unfold opNorm
  exact norm_nonneg _

theorem solution {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (Q : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ) (b : ℝ) (hb : 0 < b)
    (hIndep : iIndepFun Q Prob)
    (hBernstein : ∀ i, BernsteinConditionMatrix (Q i) Prob b)
    (δ : ℝ) (hδ : 0 < δ) :
    Prob.real {ω | δ ≤ opNorm (∑ i, Q i ω) / (n : ℝ)} ≤
      2 * (Matrix.rank (∑ i, matrixVariance (Q i) Prob) : ℝ) *
        Real.exp (-((n : ℝ) * δ ^ 2) /
          (2 * ((1 / (n : ℝ)) * opNorm (∑ i, matrixVariance (Q i) Prob) + b * δ))) := by
  by_cases hn : n = 0
  · subst hn
    have hempty : {ω : Ω | δ ≤ opNorm (∑ i : Fin 0, Q i ω) / ((0 : ℕ) : ℝ)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Nat.cast_zero, div_zero, Set.mem_empty_iff_false, iff_false, not_le]
      exact hδ
    rw [hempty, measureReal_empty]
    positivity
  · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    set V := opNorm (∑ i, matrixVariance (Q i) Prob)
    have hV : 0 ≤ V := opNorm_nonneg_aux _
    rcases eq_or_lt_of_le hV with hV0 | hV_pos
    · have hV_eq : V = 0 := hV0.symm
      let t : ℝ := 1 / (2 * b)
      have ht₀ : 0 < t := by positivity
      have htb : t * b < 1 := by
        dsimp [t]
        rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by linarith)]
        linarith
      have hlap := matrix_bernstein_laplace_mgf_bound Q b hb hIndep hBernstein δ hδ t ht₀ htb
      have hexp_eq : -((n : ℝ) * t * δ) + t ^ 2 / (2 * (1 - t * b)) * V =
          -((n : ℝ) * δ ^ 2) / (2 * ((1 / (n : ℝ)) * V + b * δ)) := by
        rw [hV_eq]
        dsimp [t]
        have hb_ne : b ≠ 0 := ne_of_gt hb
        have hδ_ne : δ ≠ 0 := ne_of_gt hδ
        field_simp
        ring
      rw [← hexp_eq]
      exact hlap
    · set σ2 : ℝ := (1 / (n : ℝ)) * V
      have hσ2_pos : 0 < σ2 := by positivity
      let t : ℝ := δ / (σ2 + b * δ)
      have hden_pos : 0 < σ2 + b * δ := by positivity
      have ht₀ : 0 < t := div_pos hδ hden_pos
      have htb : t * b < 1 := by
        dsimp [t]
        rw [div_mul_eq_mul_div, div_lt_one hden_pos]
        linarith
      have hlap := matrix_bernstein_laplace_mgf_bound Q b hb hIndep hBernstein δ hδ t ht₀ htb
      have h1mtb : 1 - t * b = σ2 / (σ2 + b * δ) := by
        dsimp [t]
        have hden_ne : σ2 + b * δ ≠ 0 := ne_of_gt hden_pos
        field_simp
        ring
      have hexp_eq : -((n : ℝ) * t * δ) + t ^ 2 / (2 * (1 - t * b)) * V =
          -((n : ℝ) * δ ^ 2) / (2 * (σ2 + b * δ)) := by
        rw [h1mtb]
        dsimp [t, σ2]
        have hden_ne : (1 / (n : ℝ)) * V + b * δ ≠ 0 := ne_of_gt hden_pos
        have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        have hV_ne : V ≠ 0 := ne_of_gt hV_pos
        field_simp
        ring
      rw [← hexp_eq]
      exact hlap
