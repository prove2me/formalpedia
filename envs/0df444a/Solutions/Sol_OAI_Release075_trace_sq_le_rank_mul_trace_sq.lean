-- Prove2me | solution 1 for OAI.Release075.trace_sq_le_rank_mul_trace_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:46:38.491984+00:00
-- url     : https://prove2.me/submissions/df6a4d7e-e8ec-4a6d-9883-4a9bf567a7e9

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L242-L264
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.trace_sq_le_rank_mul_trace_sq. The node keeps its source
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

/-- The trace-rank inequality used on a Gram matrix in the finite quotient. -/
theorem trace_sq_le_rank_mul_trace_sq {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    A.trace ^ 2 ≤ (A.rank : ℝ) * (A * A).trace := by
  classical
  have htrace : (A * A).trace = ∑ i, hA.eigenvalues i ^ 2 := by
    conv_lhs => rw [hA.spectral_theorem, ← map_mul, Matrix.diagonal_mul_diagonal,
      Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
      one_mul, Matrix.trace_diagonal]
    simp [pow_two]
  rw [hA.trace_eq_sum_eigenvalues, htrace, hA.rank_eq_card_non_zero_eigs]
  let T : Finset ι := Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0)
  have hcard : Fintype.card {i // hA.eigenvalues i ≠ 0} = T.card := by
    simp [T, Fintype.card_subtype]
  have hsum : (∑ i ∈ T, hA.eigenvalues i) = ∑ i, hA.eigenvalues i :=
    Finset.sum_filter_ne_zero _
  have hsum2 : (∑ i ∈ T, hA.eigenvalues i ^ 2) = ∑ i, hA.eigenvalues i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have : hA.eigenvalues i = 0 := by simpa [T] using hi
    simp [this]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) hA.eigenvalues
  simpa [hsum, hsum2, hcard] using hcs

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.trace_sq_le_rank_mul_trace_sq := @_root_.OAI.Release075.trace_sq_le_rank_mul_trace_sq
