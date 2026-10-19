-- Prove2me | solution 1 for OAI.Release075.tensor_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:52:04.050298+00:00
-- url     : https://prove2.me/submissions/2fa9ae29-cbd6-44bc-8e17-348da06387f2

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L521-L543
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.tensor_certificate. The node keeps its source
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

/-- Exchanging the incidence sums turns the punctured-line certificate into a
block-diagonal matrix identity. The coefficient order in each matrix is unchanged. -/
theorem tensor_certificate {P I ι κ K : Type*} [Fintype P] [Fintype I]
    [DecidableEq I] [Field K] (inc : P → Finset I) (f : P → I → K)
    (Y : I → Matrix ι κ K)
    (hline : ∀ i j k, (∑ z, if i ∈ inc z then f z j * f z k else 0) =
      -(if j = i ∧ k = i then 1 else 0)) :
    (∑ z, weightedMatrix (f z) (∑ i ∈ inc z, Y i)) = -diagonalBlocks Y := by
  classical
  ext ⟨j,a⟩ ⟨k,b⟩
  simp only [Matrix.sum_apply, weightedMatrix, Matrix.of_apply, Matrix.neg_apply,
    diagonalBlocks]
  simp only [Finset.mul_sum]
  have hsum (z : P) : (∑ i ∈ inc z, f z j * f z k * Y i a b) =
      ∑ i, (if i ∈ inc z then f z j * f z k else 0) * Y i a b := by
    simp [ite_mul]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hline, neg_mul, ite_mul, one_mul, zero_mul]
  by_cases hjk : j = k
  · subst k
    simp
  · simp [hjk, show ∀ i, ¬(j = i ∧ k = i) by rintro i ⟨rfl,rfl⟩; exact hjk rfl]

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.tensor_certificate := @_root_.OAI.Release075.tensor_certificate
