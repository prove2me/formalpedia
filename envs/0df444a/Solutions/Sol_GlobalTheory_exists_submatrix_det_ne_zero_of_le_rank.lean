-- Prove2me | solution 1 for GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:55:30.837161+00:00
-- url     : https://prove2.me/submissions/c2a1a594-2cc9-4c25-936a-22ae94169dd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNonzeroMinorOfRank
import Theorems.Thm_GlobalTheory_exists_rows_linearIndependent_of_le_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D,
        (Y.submatrix S τ).det ≠ 0 := by
  intro k _ A D _ _ _ _ ρ Y h
  obtain ⟨S, hS⟩ := exists_rows_linearIndependent_of_le_rank ρ Y h
  have hZ : (Y.submatrix S id).rank = ρ := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hS, Fintype.card_fin]
  have hZt : ρ ≤ (Y.submatrix S id)ᵀ.rank := by rw [Matrix.rank_transpose, hZ]
  obtain ⟨τ, hτ⟩ := exists_rows_linearIndependent_of_le_rank ρ (Y.submatrix S id)ᵀ hZt
  refine ⟨S, τ, ?_⟩
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hτ)
  have e : (Y.submatrix S id)ᵀ.submatrix τ id = (Y.submatrix S τ)ᵀ := by ext i j; rfl
  rw [e, Matrix.det_transpose] at hu
  exact hu.ne_zero
end GlobalTheory
