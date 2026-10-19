-- Prove2me | solution 1 for OAI.ProjectionMoments.rows_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:25:31.938323+00:00
-- url     : https://prove2.me/submissions/311a09cc-aa41-400f-bc96-c44fbb88bd77

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Frames.lean:L135-L170
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.rows_factor. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames

-- ---- from OAI.Probability.GaussianRegression.Gram ----
namespace OAI

/-!
Gram determinants, orthogonal distances, and product integration.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
variable (n : ℕ)
lemma gsUpper_expansion (v : Fin n → E) (j : Fin n) :
    ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i = v j := by
  simp only [gsUpper, add_smul, Finset.sum_add_distrib]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs => rw [gramSchmidt_def'' ℝ v j]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

lemma gsUpper_det (v : Fin n → E) : (gsUpper n v).det = 1 := by
  have htri : (gsUpper n v).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [gsUpper, (ne_of_gt hij), (not_lt_of_ge hij.le)]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gsUpper]

end GramFactorization

section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
variable [MeasurableSpace E] [BorelSpace E]
end GramDistances

variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Frames ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
attribute [fun_prop] measurable_lowerDensity

section Rotations
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {E}

variable [MeasurableSpace E] [BorelSpace E]

end Rotations

section Triangular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowJacobian_pos [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} {A : Fin m → E} (hA : LinearIndependent ℝ A) :
    0 < rowJacobian A := Finset.prod_pos (fun i _ => norm_pos_iff.mpr (gramSchmidt_ne_zero i hA))

lemma rows_factor {m : ℕ} (A : Fin m → E) (hA : LinearIndependent ℝ A) :
    ∃ u : Fin m → E, Orthonormal ℝ u ∧
      ∃ T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ),
        (∀ x, coordinateMap A x = T (coordinateMap u x)) ∧
        (volume : Measure (Fin m → ℝ)).map T =
          (ENNReal.ofReal (rowJacobian A))⁻¹ • volume := by
  let u := gramSchmidtNormed ℝ A
  let R : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.diagonal (fun i => ‖gramSchmidt ℝ A i‖) * NoiselessRegression.gsUpper m A
  have hu : Orthonormal ℝ u := gramSchmidtNormed_orthonormal hA
  have hn (i : Fin m) : ‖gramSchmidt ℝ A i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hA)
  have hexp (j : Fin m) : ∑ i, R i j • u i = A j := by
    rw [← NoiselessRegression.gsUpper_expansion m A j]
    apply Finset.sum_congr rfl
    intro i _
    simp only [R, u, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
    congr 1
    simp [hn i, mul_comm]
  have hdet : R.transpose.det = rowJacobian A := by
    dsimp only [R, rowJacobian]
    rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal,
      NoiselessRegression.gsUpper_det, mul_one]
  have hd : R.transpose.det ≠ 0 := by rw [hdet]; exact (rowJacobian_pos hA).ne'
  let T := (R.transpose.toLinearEquiv' (Matrix.invertibleOfIsUnitDet R.transpose (isUnit_iff_ne_zero.mpr hd))).toContinuousLinearEquiv
  refine ⟨u, hu, T, ?_, ?_⟩
  · intro x
    ext j
    rw [coordinateMap_apply, ← hexp j]
    change ⟪x, ∑ i, R i j • u i⟫ = Matrix.mulVec R.transpose (coordinateMap u x) j
    simp only [inner_sum, inner_smul_right, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, coordinateMap_apply]
  · change (volume : Measure (Fin m → ℝ)).map (Matrix.toLin' R.transpose) = _
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hd,
      abs_of_pos (inv_pos.mpr (by rw [hdet]; exact rowJacobian_pos hA)), hdet,
      ENNReal.ofReal_inv_of_pos (rowJacobian_pos hA)]

end Triangular

section CoordinateDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.rows_factor := @_root_.OAI.ProjectionMoments.rows_factor
