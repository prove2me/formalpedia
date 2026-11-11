-- Prove2me | solution 1 for MulticalibrationGGM.Reduction.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T06:18:17.790218+00:00
-- url     : https://prove2.me/submissions/c0e4d01f-3cda-4f24-a50b-86a1a9bd2294

import Mathlib
import Definitions.Def_MulticalibrationGGM_Reduction_Algorithm

open scoped NNReal

open MulticalibrationGGM.Reduction

theorem solution {X S Q : Type*} {d : ℕ} (Y : Set (Vector d))
    (hYcompact : IsCompact Y) (hYconvex : Convex ℝ Y)
    (H : Set (Test X Y)) (hHbounded : BoundedTests H)
    (A : OnlineLearner H S) (O : EVIOracle X Y H Q) (N : Nature X Y H)
    (ε : ℕ → ℝ≥0) (T : ℕ)
    (hvalid : ValidPrefix (algorithmRound A O N ε) T) (h : H) :
    mcError (algorithmRound A O N ε) T h ≤
      comparatorRegret (algorithmRound A O N ε) T h + eviError (algorithmRound A O N ε) T := by
  let R := algorithmRound A O N ε
  have hround (t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
      expectedPayoff (R t).test.val (R t).context (R t).forecast (R t).outcome ≤
        ((R t).tolerance : ℝ) := by
    exact ((hvalid t ht).1 (R t).outcome).2
  have hsum := Finset.sum_le_sum hround
  change mcError R T h ≤ comparatorRegret R T h + eviError R T
  simp only [mcError, comparatorRegret, OnlineLearningOCO.FoReL.regret,
    feedback, eviError, Finset.sum_neg_distrib]
  linarith

#print axioms solution
