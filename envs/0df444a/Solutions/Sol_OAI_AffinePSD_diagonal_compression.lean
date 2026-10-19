-- Prove2me | solution 1 for OAI.AffinePSD.diagonal_compression
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:26:18.603615+00:00
-- url     : https://prove2.me/submissions/bd02aabd-54d5-4832-9e81-0d807a3c57c0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PSDCompression.lean:L23-L61
-- (upload_full_project.md Phase 4): solution for node OAI.AffinePSD.diagonal_compression. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation

-- ---- from OAI.Combinatorics.MatchingPSD.PSDCompression ----
namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma zero_col_of_diag_zero {A : Matrix R R ℝ} (hA : A.PosSemidef)
    (i : R) (hi : A i i = 0) (j : R) : A j i = 0 := by
  have h := (hA.dotProduct_mulVec_zero_iff (x := Pi.single i 1)).mp (by simpa using hi)
  simpa using congrFun h j

lemma zero_row_of_diag_zero {A : Matrix R R ℝ} (hA : A.PosSemidef)
    (i : R) (hi : A i i = 0) (j : R) : A i j = 0 := by
  have hs : A i j = A j i := by
    simpa using congrArg (fun M : Matrix R R ℝ => M j i) hA.isHermitian.eq
  rw [hs]
  exact zero_col_of_diag_zero hA i hi j

lemma diagonal_compression (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (d : R → ℝ) (hs : ∑ i, B i = diagonal d) (A : Matrix R R ℝ)
    (hA : A.PosSemidef) :
    ∃ A' : Matrix R R ℝ, A'.PosSemidef ∧ evaluation B A' = evaluation B A ∧
      (∀ j, d j = 0 → A' j j = 0) := by
  classical
  let p : R → ℝ := fun j => if d j = 0 then 0 else 1
  let P := diagonal p
  have hdiag (i : I) (j : R) (hj : d j = 0) : B i j j = 0 := by
    have hle : B i j j ≤ ∑ k, B k j j :=
      Finset.single_le_sum (fun k _ => (hB k).diag_nonneg) (Finset.mem_univ i)
    have he : ∑ k, B k j j = d j := by
      simpa only [Matrix.sum_apply, Matrix.diagonal_apply_eq] using
        congrArg (fun M : Matrix R R ℝ => M j j) hs
    have hn := (hB i).diag_nonneg (i := j)
    rw [he, hj] at hle
    exact le_antisymm hle hn
  have hpB (i : I) : P * B i = B i := by
    ext j k
    simp only [P, Matrix.diagonal_mul, p]
    split_ifs with hj
    · simp [zero_row_of_diag_zero (hB i) j (hdiag i j hj) k]
    · simp
  have hBp (i : I) : B i * P = B i := by
    ext j k
    simp only [P, Matrix.mul_diagonal, p]
    split_ifs with hk
    · simp [zero_col_of_diag_zero (hB i) k (hdiag i k hk) j]
    · simp
  refine ⟨P * A * P, ?_, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, P, Matrix.diagonal_transpose]
      using hA.conjTranspose_mul_mul_same P
  · ext i
    change (P * A * P * B i).trace = (A * B i).trace
    rw [Matrix.mul_assoc P A P, Matrix.mul_assoc P (A * P) (B i),
      Matrix.trace_mul_comm P, Matrix.mul_assoc A P (B i), hpB,
      Matrix.mul_assoc A (B i) P, hBp]
  · intro j hj
    simp [P, Matrix.mul_diagonal, Matrix.diagonal_mul, p, hj]

end AffinePSD

end OAI

-- ---- platform node ----
open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.AffinePSD.diagonal_compression := @_root_.OAI.AffinePSD.diagonal_compression
