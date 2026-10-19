-- Prove2me | solution 1 for OAI.Release075.quotientMatrix_sum_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:53:27.976736+00:00
-- url     : https://prove2.me/submissions/e1a4ca40-c1ec-4b5b-a659-3dedcd65b39e

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L559-L584
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.quotientMatrix_sum_rank_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- A local Cartesian block factors through one copy of the finite regular module. -/
theorem quotientMatrix_sum_rank_le {ι s t F K : Type*} [Fintype ι]
    [Fintype s] [Fintype t] [Group F] [Fintype F] [DecidableEq F] [Field K]
    (L : ι → s → F) (R : ι → t → F) :
    (∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k)).rank ≤
      Fintype.card F := by
  classical
  let A : Matrix (ι × F) F K := Matrix.of fun x a =>
    (∑ j, regularMatrix (R := K) (L x.1 j)⁻¹) x.2 a
  let B : Matrix F (ι × F) K := Matrix.of fun b y =>
    (∑ k, regularMatrix (R := K) (R y.1 k)) b y.2
  have hfactor :
      (∑ j : s, ∑ k : t, quotientMatrix (R := K) (fun u v => (L u j)⁻¹ * R v k)) =
      A * B := by
    ext ⟨u,a⟩ ⟨v,b⟩
    simp only [Matrix.sum_apply, quotientMatrix, flattenMatrix_apply, Matrix.of_apply,
      map_mul, Matrix.mul_apply, A, B]
    simp only [Finset.sum_mul, Finset.mul_sum]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset t))
      (t := (Finset.univ : Finset F))]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm
  rw [hfactor]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.quotientMatrix_sum_rank_le := @_root_.OAI.Release075.quotientMatrix_sum_rank_le
