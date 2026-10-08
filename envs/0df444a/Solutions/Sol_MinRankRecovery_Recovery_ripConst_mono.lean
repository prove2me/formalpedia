-- Prove2me | solution 1 for MinRankRecovery.Recovery.ripConst_mono
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:46:59.762291+00:00
-- url     : https://prove2.me/submissions/28837bb8-c7e8-4620-8df6-4e3ecc82f722

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- §3, p. 12: `δ_r(𝒜) ≤ δ_{r'}(𝒜)` for `r ≤ r'`. -/
theorem ripConst_mono {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) {r r' : ℕ}
    (h : r ≤ r') : ripConst Xs r ≤ ripConst Xs r' := by
  classical
  let C : ℝ := Real.sqrt (∑ i, ∑ j, ∑ k, (Xs i j k) ^ 2)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = ∑ i, ∑ j, ∑ k, (Xs i j k) ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  have bound (X : Matrix (Fin m) (Fin n) ℝ) :
      measNorm Xs X ≤ C * frobeniusNorm X := by
    have hF := Real.sqrt_nonneg (∑ j, ∑ k, (X j k) ^ 2)
    have hFsq := Real.sq_sqrt (show 0 ≤ ∑ j, ∑ k, (X j k) ^ 2 by positivity)
    have hQ := Real.sqrt_nonneg (∑ i, (observationOp Xs X i) ^ 2)
    have hQsq := Real.sq_sqrt (show 0 ≤ ∑ i, (observationOp Xs X i) ^ 2 by positivity)
    have hsum : (∑ i, (observationOp Xs X i) ^ 2) ≤
        (∑ i, ∑ j, ∑ k, (Xs i j k) ^ 2) * (∑ j, ∑ k, (X j k) ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have hc := Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (Fin m × Fin n))
        (fun jk => Xs i jk.1 jk.2) (fun jk => X jk.1 jk.2)
      simpa [observationOp, traceInner, Fintype.sum_prod_type] using hc
    dsimp [measNorm, frobeniusNorm]
    have hp := mul_nonneg hC hF
    nlinarith [sq_nonneg (C * Real.sqrt (∑ j, ∑ k, (X j k)^2) +
      Real.sqrt (∑ i, (observationOp Xs X i)^2))]
  have nonempty (s : ℕ) :
      ({δ : ℝ | 0 ≤ δ ∧ ∀ X : Matrix (Fin m) (Fin n) ℝ, X.rank ≤ s →
        (1-δ)*frobeniusNorm X ≤ measNorm Xs X ∧
          measNorm Xs X ≤ (1+δ)*frobeniusNorm X}).Nonempty := by
    refine ⟨C+1, by positivity, ?_⟩
    intro X _
    have hf : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
    have hm : 0 ≤ measNorm Xs X := Real.sqrt_nonneg _
    have hb := bound X
    constructor
    · nlinarith [mul_nonneg hC hf]
    · nlinarith
  unfold ripConst
  apply le_csInf (nonempty r')
  intro δ hδ
  apply csInf_le
  · exact ⟨0, fun x hx => hx.1⟩
  · exact ⟨hδ.1, fun X hX => hδ.2 X (hX.trans h)⟩


end MinRankRecovery.Recovery

theorem solution {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) {r r' : ℕ}
    (h : r ≤ r') : MinRankRecovery.Recovery.ripConst Xs r ≤ MinRankRecovery.Recovery.ripConst Xs r' :=
  MinRankRecovery.Recovery.ripConst_mono Xs h

#print axioms solution
