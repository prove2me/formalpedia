-- Prove2me | solution 1 for HighDimStat.RandomMatrices.matrix_bernstein_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:29:39.161642+00:00
-- url     : https://prove2.me/submissions/7d160cf6-fb5c-4417-803c-fc1960a10ba7

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_BernsteinConditionMatrix
import Definitions.Def_HighDimStat_RandomMatrices_matrixVariance
import Definitions.Def_HighDimStat_RandomMatrices_opNorm

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

noncomputable instance aux_mbb_instMeasurableSpaceMatrix {d : ℕ} :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := by
  unfold Matrix; infer_instance

/-- The zero random `0 × 0` matrix on the one-point probability space satisfies the matrix
Bernstein condition for every parameter `b`. -/
lemma aux_mbb_bernstein_zero (b : ℝ) :
    BernsteinConditionMatrix (fun _ : Unit => (0 : Matrix (Fin 0) (Fin 0) ℝ))
      (Measure.dirac ()) b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall (fun _ => Subsingleton.elim _ _)
  · intro j i; exact i.elim0
  · exact Subsingleton.elim _ _
  · intro j _
    unfold LoewnerLE
    rw [Subsingleton.elim (_ - _) (0 : Matrix (Fin 0) (Fin 0) ℝ)]
    exact Matrix.PosSemidef.zero

/-- Every `0 × 0` real matrix has rank zero. -/
lemma aux_mbb_rank_fin_zero (M : Matrix (Fin 0) (Fin 0) ℝ) : M.rank = 0 := by
  rw [Subsingleton.elim M 0, Matrix.rank_zero]

/-- The operator norm is nonnegative. -/
lemma aux_mbb_opNorm_nonneg {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ opNorm M := by
  unfold opNorm; exact norm_nonneg _

end HighDimStat.RandomMatrices

open HighDimStat.RandomMatrices

theorem solution : ¬ (∀ {n d : ℕ} {Ω : Type} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (Q : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ) (b : ℝ) (hb : 0 < b)
    (hIndep : iIndepFun Q Prob)
    (hBernstein : ∀ i, BernsteinConditionMatrix (Q i) Prob b)
    (δ : ℝ) (hδ : 0 ≤ δ),
    Prob.real {ω | δ ≤ opNorm (∑ i, Q i ω) / (n : ℝ)} ≤
      2 * (Matrix.rank (∑ i, matrixVariance (Q i) Prob) : ℝ) *
        Real.exp (-((n : ℝ) * δ ^ 2) /
          (2 * ((1 / (n : ℝ)) * opNorm (∑ i, matrixVariance (Q i) Prob) + b * δ)))) := by
  intro h
  have key := @h 1 0 Unit _ (Measure.dirac ()) _
    (fun _ _ => (0 : Matrix (Fin 0) (Fin 0) ℝ)) 1 one_pos iIndepFun.of_subsingleton
    (fun _ => aux_mbb_bernstein_zero 1) 0 le_rfl
  rw [aux_mbb_rank_fin_zero] at key
  have hset : {ω : Unit | (0 : ℝ) ≤
      opNorm (∑ i : Fin 1, (fun (_ : Fin 1) (_ : Unit) => (0 : Matrix (Fin 0) (Fin 0) ℝ)) i ω) /
        ((1 : ℕ) : ℝ)} = Set.univ :=
    Set.eq_univ_of_forall fun _ => div_nonneg (aux_mbb_opNorm_nonneg _) (Nat.cast_nonneg _)
  rw [hset, probReal_univ] at key
  norm_num at key
