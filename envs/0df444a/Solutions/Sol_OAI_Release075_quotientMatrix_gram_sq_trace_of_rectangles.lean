-- Prove2me | solution 1 for OAI.Release075.quotientMatrix_gram_sq_trace_of_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:47:58.51452+00:00
-- url     : https://prove2.me/submissions/711a75a3-6083-4c2e-81f3-fb402b0afe94

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L375-L400
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.quotientMatrix_gram_sq_trace_of_rectangles. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace Release075

universe u v

open scoped BigOperators

theorem flattenMatrix_mul {ι κ τ F R : Type*} [Fintype κ] [Fintype F]
    [DecidableEq F] [Semiring R] (A : Matrix ι κ (Matrix F F R))
    (B : Matrix κ τ (Matrix F F R)) :
    flattenMatrix (A * B) = flattenMatrix A * flattenMatrix B := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [flattenMatrix, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]

theorem flattenMatrix_transpose {ι κ α β R : Type*}
    (A : Matrix ι κ (Matrix α β R)) :
    (flattenMatrix A).transpose = flattenMatrix (Matrix.of fun i j => (A j i).transpose) := rfl

theorem flattenMatrix_trace {ι F R : Type*} [Fintype ι] [Fintype F]
    [AddCommMonoid R] (A : Matrix ι ι (Matrix F F R)) :
    (flattenMatrix A).trace = ∑ i, (A i i).trace := by
  simp [Matrix.trace, Fintype.sum_prod_type, flattenMatrix]

theorem quotientMatrix_gram {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    quotientMatrix (R := R) g * (quotientMatrix g).transpose =
      flattenMatrix (Matrix.of fun u u' => ∑ v, regularMatrix (g u v * (g u' v)⁻¹)) := by
  rw [quotientMatrix, flattenMatrix_transpose, ← flattenMatrix_mul]
  congr 1
  ext u u' a b
  simp [Matrix.of_apply, Matrix.mul_apply, Matrix.sum_apply, ← map_mul]

/-- The second trace expansion, before counting degenerate rectangles. -/
theorem quotientMatrix_gram_sq_trace {ι F R : Type*} [Fintype ι] [Group F]
    [Fintype F] [DecidableEq F] [Semiring R] (g : ι → ι → F) :
    ((quotientMatrix (R := R) g * (quotientMatrix g).transpose) *
      (quotientMatrix g * (quotientMatrix g).transpose)).trace =
        ∑ u, ∑ u', ∑ v, ∑ v', (regularMatrix (R := R)
          (g u v * (g u' v)⁻¹ * g u' v' * (g u v')⁻¹)).trace := by
  rw [quotientMatrix_gram, ← flattenMatrix_mul, flattenMatrix_trace]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.sum_mul, Matrix.mul_sum, ← map_mul,
    Matrix.trace_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro u' _
  exact Finset.sum_comm

/-- The exact count `2r^3-r^2` of degenerate index choices. -/
theorem quotientMatrix_gram_sq_trace_of_rectangles {ι F R : Type*} [Fintype ι]
    [Group F] [Fintype F] [DecidableEq F] [CommRing R]
    (g : ι → ι → F) (hg : RectanglesSurvive g) :
    ((quotientMatrix (R := R) g * (quotientMatrix g).transpose) *
      (quotientMatrix g * (quotientMatrix g).transpose)).trace =
      (2 * (Fintype.card ι : R) ^ 3 - (Fintype.card ι : R) ^ 2) * Fintype.card F := by
  classical
  rw [quotientMatrix_gram_sq_trace]
  have ht (u u' v v' : ι) :
      (regularMatrix (R := R) (g u v * (g u' v)⁻¹ * g u' v' * (g u v')⁻¹)).trace =
      (if u = u' then (Fintype.card F : R) else 0) +
      (if v = v' then (Fintype.card F : R) else 0) -
      (if u = u' ∧ v = v' then (Fintype.card F : R) else 0) := by
    by_cases hu : u = u'
    · subst u'
      simp only [mul_inv_cancel, one_mul, regularMatrix_trace,
        true_and, add_sub_cancel_right]
    · by_cases hv : v = v'
      · subst v'
        simp [mul_assoc, hu]
      · simp only [regularMatrix_trace, ite_eq_right (hg u u' v v' hu hv), ite_eq_right hu,
          ite_eq_right hv, ite_eq_right (not_and.mpr (fun h => (hu h).elim)), add_zero, sub_zero]
  simp only [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_and]
  simp [pow_succ, mul_assoc, sub_mul]
  ring

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.quotientMatrix_gram_sq_trace_of_rectangles := @_root_.OAI.Release075.quotientMatrix_gram_sq_trace_of_rectangles
