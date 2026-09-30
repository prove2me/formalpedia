-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_direction_A_conjugacy_step
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T11:01:37.899743+00:00
-- url     : https://prove2.me/submissions/b41a8f6d-1405-49d4-82dc-769b58ed2863

import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

open Matrix LimitedBFGS.SQN

theorem solution : ¬ (∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef →
    ∀ (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (k : ℕ),
    (pcgIter A b H₀ x₀ (k+1)).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ k).d) = 0) := by
  intro h
  have hh := h (n := 2) 1 (Matrix.PosDef.one) ![1,0] !![0,1;1,0] 0 0
  norm_num [pcgIter,exactStep,grad,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hh
