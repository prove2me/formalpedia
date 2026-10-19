-- Prove2me | solution 2 for OAI.HyperedgeComparison.inverse_last_diag_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:11:23.32602+00:00
-- url     : https://prove2.me/submissions/37c79326-69d7-46fa-ab69-4dab00fc3d6d

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean:L1378-L1395
-- (upload_full_project.md Phase 4): solution for node OAI.HyperedgeComparison.inverse_last_diag_mul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Theorems.Thm_OAI_HyperedgeComparison_baseMatrix_diag_pos

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

section FiniteLaw
variable [Fintype E]

theorem baseMatrix_lowerTriangular {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) : (baseMatrix H p x).IsLowerTriangular := by
  intro i j hij
  have hf (ω : E → Bool) : ¬firstRoot H x ω ∅ j i := by
    intro hf
    exact Set.disjoint_left.mp hf.1 hf.2 ⟨i, hij, rfl⟩
  simp [baseMatrix, column, hf]

theorem baseMatrix_det_ne_zero {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) :
    (baseMatrix H p x).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (baseMatrix_lowerTriangular H p x)]
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => ne_of_gt (baseMatrix_diag_pos H p hp x hx k))

/-- The final diagonal entry of the inverse is reciprocal to the probability
of avoiding all preceding listed vertices. -/
theorem inverse_last_diag_mul {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n + 1) → V) (hx : Function.Injective x) :
    (baseMatrix H p x)⁻¹ (Fin.last n) (Fin.last n) *
      baseMatrix H p x (Fin.last n) (Fin.last n) = 1 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
    M (Fin.last n) (Fin.last n)) (Matrix.nonsing_inv_mul (baseMatrix H p x) hdet)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_single (Fin.last n)] at h
  · exact h
  · intro j _ hj
    have hjl : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hj
    exact mul_eq_zero_of_right _ (baseMatrix_lowerTriangular H p x hjl)
  · simp

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

end Site

end HyperedgeComparison

end OAI

-- ---- platform node ----
open OAI OAI.HyperedgeComparison
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix


theorem solution.{uE,uV} : type_of% @_root_.OAI.HyperedgeComparison.inverse_last_diag_mul.{uE,uV} := @_root_.OAI.HyperedgeComparison.inverse_last_diag_mul.{uE,uV}
