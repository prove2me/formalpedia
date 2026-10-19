-- Prove2me | solution 1 for OAI.Release075.sum_rank_le_rank_diagonalBlocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:49:27.44798+00:00
-- url     : https://prove2.me/submissions/a1746322-6cd4-4eee-9b8f-e23db398f0e9

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L470-L496
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.sum_rank_le_rank_diagonalBlocks. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Theorems.Thm_OAI_Release075_exists_full_rank_minor

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- The lower rank bound for a direct sum, proved by its full-rank block minors. -/
theorem sum_rank_le_rank_diagonalBlocks {I ι κ K : Type*} [Fintype I]
    [Fintype ι] [Fintype κ] [DecidableEq I] [Field K]
    (Y : I → Matrix ι κ K) : (∑ i, (Y i).rank) ≤ (diagonalBlocks Y).rank := by
  classical
  choose f g hf hg hdet using fun i => exists_full_rank_minor (Y i)
  let B : ∀ i, Matrix (Fin (Y i).rank) (Fin (Y i).rank) K :=
    fun i => (Y i).submatrix (f i) (g i)
  let rows : (Σ i, Fin (Y i).rank) → I × ι := fun x => (x.1, f x.1 x.2)
  let cols : (Σ i, Fin (Y i).rank) → I × κ := fun x => (x.1, g x.1 x.2)
  have hminor : (diagonalBlocks Y).submatrix rows cols = Matrix.blockDiagonal' B := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hij : i = j
    · subst j
      simp [diagonalBlocks, rows, cols, B]
    · simp [diagonalBlocks, rows, cols, Matrix.blockDiagonal'_apply_ne _ _ _ hij, hij]
  have hBunit : IsUnit B := Pi.isUnit_iff.mpr (fun i =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hdet i)))
  have hunit : IsUnit (Matrix.blockDiagonal' B) :=
    hBunit.map (Matrix.blockDiagonal'RingHom (fun i => Fin (Y i).rank) K)
  have hrank := Matrix.rank_of_isUnit (Matrix.blockDiagonal' B) hunit
  calc
    (∑ i, (Y i).rank) = Fintype.card (Σ i, Fin (Y i).rank) := by simp
    _ = (Matrix.blockDiagonal' B).rank := hrank.symm
    _ ≤ (diagonalBlocks Y).rank := by
      rw [← hminor]
      exact Matrix.rank_submatrix_le _ _ _

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.sum_rank_le_rank_diagonalBlocks := @_root_.OAI.Release075.sum_rank_le_rank_diagonalBlocks
