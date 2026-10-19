-- Prove2me | solution 1 for OAI.AffinePSD.diagonal_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:27:39.415472+00:00
-- url     : https://prove2.me/submissions/46706c3d-9c92-44b4-a2ad-6062ded9bedd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PSDCompression.lean:L80-L98
-- (upload_full_project.md Phase 4): solution for node OAI.AffinePSD.diagonal_trace_bound. The node keeps its source
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

omit [Fintype R] in
lemma sum_diagonal_nonneg (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (d : R → ℝ) (hs : ∑ i, B i = diagonal d) : ∀ j, 0 ≤ d j := by
  intro j
  have he : ∑ i, B i j j = d j := by
    simpa only [Matrix.sum_apply, Matrix.diagonal_apply_eq] using
      congrArg (fun M : Matrix R R ℝ => M j j) hs
  rw [← he]
  exact Finset.sum_nonneg (fun i _ => (hB i).diag_nonneg)

lemma evaluation_sum_eq (B : I → Matrix R R ℝ) (d : R → ℝ)
    (hs : ∑ i, B i = diagonal d) (A : Matrix R R ℝ) :
    ∑ i, evaluation B A i = ∑ j, A j j * d j := by
  simp only [evaluation_apply]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, hs]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]

lemma diagonal_trace_bound (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (d : R → ℝ) (hs : ∑ i, B i = diagonal d) (A : Matrix R R ℝ)
    (hA : A.PosSemidef) (hz : ∀ j, d j = 0 → A j j = 0) :
    A.trace ≤ (∑ j, (d j)⁻¹) * ∑ i, evaluation B A i := by
  have hd := sum_diagonal_nonneg B hB d hs
  have he := evaluation_sum_eq B d hs A
  rw [he]
  change (∑ j, A j j) ≤ _
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : d j = 0
  · simp [hj, hz j hj]
  · have hp : 0 < d j := lt_of_le_of_ne (hd j) (Ne.symm hj)
    have hle : A j j * d j ≤ ∑ k, A k k * d k :=
      Finset.single_le_sum (fun k _ => mul_nonneg (hA.diag_nonneg (i := k)) (hd k)) (Finset.mem_univ j)
    calc
      A j j = (d j)⁻¹ * (A j j * d j) := by field_simp
      _ ≤ (d j)⁻¹ * ∑ k, A k k * d k := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hp.le)

end AffinePSD

end OAI

-- ---- platform node ----
open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.AffinePSD.diagonal_trace_bound := @_root_.OAI.AffinePSD.diagonal_trace_bound
