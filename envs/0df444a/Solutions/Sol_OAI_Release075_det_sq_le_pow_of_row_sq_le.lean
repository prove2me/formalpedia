-- Prove2me | solution 1 for OAI.Release075.det_sq_le_pow_of_row_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:43:34.041162+00:00
-- url     : https://prove2.me/submissions/4c05d574-74f6-450e-9f61-e28f136cf9b1

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L159-L175
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.det_sq_le_pow_of_row_sq_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075

universe u v

open scoped BigOperators

theorem det_abs_le_prod_row_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (A i)
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le v
  rw [b.toBasis.orientation.volumeForm_robust b rfl] at h
  have hmat : b.toBasis.toMatrix v = A.transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, b, v, Matrix.transpose_apply]
  simpa [Module.Basis.det_apply, hmat, Matrix.det_transpose, v] using h

/-- The squared form of Hadamard's inequality avoids fractional exponents. -/
theorem det_sq_le_pow_of_row_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ) (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ r) : A.det ^ 2 ≤ r ^ n := by
  have h := det_abs_le_prod_row_norm A
  have hsquare : A.det ^ 2 ≤
      (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg A.det) h 2
  rw [← Finset.prod_pow] at hsquare
  apply hsquare.trans
  calc
    (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ ^ 2)
        ≤ ∏ _i : Fin n, r := by
      apply Finset.prod_le_prod₀
      · intro i _; positivity
      · intro i _
        simpa only [EuclideanSpace.real_norm_sq_eq] using hrow i
    _ = r ^ n := by simp

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.det_sq_le_pow_of_row_sq_le := @_root_.OAI.Release075.det_sq_le_pow_of_row_sq_le
