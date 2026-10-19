-- Prove2me | solution 1 for OAI.ProjectionMoments.normalizedDensity_unitBall
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:03:51.236994+00:00
-- url     : https://prove2.me/submissions/b0f3be12-bddd-4f24-825b-2c76e09294b9

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/CapDuality.lean:L56-L71
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.normalizedDensity_unitBall. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Theorems.Thm_OAI_ProjectionMoments_ballAverage_eq
import Theorems.Thm_OAI_ProjectionMoments_lowerDensity_is_density

-- ---- from OAI.Probability.ProjectionMoments.Graph ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

section GaussianGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianGraph

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ballAverage_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R η : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R + η < ‖y - rowMap A z‖) :
    ballAverage ν m η (A,y) = 0 := by
  have hz : (ν.map (rowMap A)) (Metric.closedBall y η) = 0 := by
    rw [Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ν.support_mem_ae] with t ht hty
    have htR : ‖t-z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hsupport ht
    have hty' : ‖y - rowMap A t‖ ≤ η := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hty
    have hn : ‖rowMap A t - rowMap A z‖ ≤ ‖rowMap A‖ * R := by
      rw [← map_sub]
      exact ((rowMap A).le_opNorm _).trans (mul_le_mul_of_nonneg_left htR (norm_nonneg _))
    have hb : ‖y - rowMap A z‖ ≤ η + ‖rowMap A‖ * R := by
      calc
        _ = ‖(y - rowMap A t) + (rowMap A t - rowMap A z)‖ := by congr 1; abel
        _ ≤ ‖y - rowMap A t‖ + ‖rowMap A t - rowMap A z‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hty' hn
    linarith
  simp only [ballAverage_eq, hz, ENNReal.zero_div]

theorem lowerDensity_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R < ‖y - rowMap A z‖) :
    lowerDensity ν m (A,y) = 0 := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : ∀ᶠ n : ℕ in atTop, ballAverage ν m ((n : ℝ) + 1)⁻¹ (A,y) = 0 := by
    filter_upwards [ht (Iio_mem_nhds (sub_pos.mpr hfar))] with n hn
    apply ballAverage_eq_zero_of_far ν m A z R _ y hsupport
    have hnn : ((n : ℝ) + 1)⁻¹ < ‖y - rowMap A z‖ - ‖rowMap A‖ * R := hn
    linarith
  exact (liminf_congr he).trans (liminf_const _)
end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
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
lemma norm_rowMap_le [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} {u : Fin m → E} (hu : Orthonormal ℝ u) :
    ‖rowMap u‖ ≤ 1 := by
  apply (rowMap u).opNorm_le_bound zero_le_one
  intro x
  rw [one_mul]
  have h := hu.sum_inner_products_le (x := x) (s := Finset.univ)
  apply (sq_le_sq₀ (norm_nonneg (rowMap u x)) (norm_nonneg x)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [rowMap_apply, Real.norm_eq_abs, sq_abs,
    WithLp.ofLp_toLp, real_inner_comm] using h

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

-- ---- from OAI.Probability.ProjectionMoments.Polar ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gram_mixRows [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) :
    Matrix.gram ℝ (mixRows M X) = M * Matrix.gram ℝ X * M.transpose := by
  ext i j
  simp only [Matrix.gram_apply, mixRows, inner_sum, sum_inner, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_squared [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) :
    polarRadial X * polarRadial X = Matrix.gram ℝ X :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_gram ℝ X).nonneg

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_pos [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) : 0 ≤ polarRadial X := CFC.sqrt_nonneg _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_isUnit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    IsUnit (polarRadial X) :=
  (CFC.isUnit_sqrt_iff _ (Matrix.posSemidef_gram ℝ X).nonneg).mpr
    (Matrix.posDef_gram_iff_linearIndependent.mpr hX).isUnit

lemma rawPolarRows_orthonormal {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    Orthonormal ℝ (rawPolarRows X) := by
  have hH := polarRadial_isUnit hX
  have hdet : IsUnit (polarRadial X).det := (Matrix.isUnit_iff_isUnit_det _).mp hH
  have hsym : (polarRadial X)⁻¹.transpose = (polarRadial X)⁻¹ := by
    have hh : (polarRadial X).IsHermitian := (polarRadial_pos X).isSelfAdjoint
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh.inv
  have hgram : Matrix.gram ℝ (rawPolarRows X) = 1 := by
    rw [rawPolarRows, gram_mixRows, hsym, ← polarRadial_squared,
      ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul, Matrix.mul_nonsing_inv _ hdet]
  apply orthonormal_iff_ite.mpr
  intro i j
  simpa only [Matrix.gram_apply, Matrix.one_apply] using congrFun (congrFun hgram i) j

lemma polarRows_orthonormal {k : ℕ} {u : Fin k → E} (hu : Orthonormal ℝ u)
    (X : Fin k → E) : Orthonormal ℝ (polarRows u X) := by
  by_cases hX : LinearIndependent ℝ X
  · simpa only [polarRows, ite_eq_left hX] using rawPolarRows_orthonormal hX
  · simpa only [polarRows, ite_eq_right hX] using hu

end

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.BallMoments ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_polarRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma normalizedDensity_support (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (hu : Orthonormal ℝ u) (hs : ν.support ⊆ Metric.closedBall 0 1)
    (X : Fin k → E) (y : Label k) (hy : 1 < ‖y‖) : normalizedDensity ν k u (X,y) = 0 := by
  have h := lowerDensity_eq_zero_of_far ν k (polarRows u X) 0 1 y hs
    (by simpa only [map_zero, sub_zero, mul_one] using (norm_rowMap_le (polarRows_orthonormal hu X)).trans_lt hy)
  simp only [normalizedDensity, h, mul_zero]

lemma normalizedDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (X : Fin k → E)
    (h : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    ((unitBallVolume k)⁻¹ • (volume : Measure (Label k))).withDensity
      (fun y => normalizedDensity ν k u (X,y)) = ν.map (rowMap (polarRows u X)) := by
  rw [withDensity_smul_measure]
  change (unitBallVolume k)⁻¹ • volume.withDensity
    (unitBallVolume k • (fun y => lowerDensity ν k (polarRows u X,y))) = _
  rw [withDensity_smul _ (by fun_prop), smul_smul,
    ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k), one_smul]
  exact lowerDensity_is_density ν k _ h

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.CapDuality ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma normalizedDensity_unitBall (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    {u : Fin k → E} (hu : Orthonormal ℝ u) (hs : ν.support ⊆ Metric.closedBall 0 1)
    (X : Fin k → E) (hac : ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    (unitBallLaw k).withDensity (fun y => normalizedDensity ν k u (X,y)) =
      ν.map (rowMap (polarRows u X)) := by
  have he : (Metric.closedBall (0:Label k) 1).indicator
      (fun y => normalizedDensity ν k u (X,y)) = fun y => normalizedDensity ν k u (X,y) := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0:Label k) 1
    · simp [hy]
    · rw [Set.indicator_of_notMem hy]
      have hh : 1 < ‖y‖ := by simpa using hy
      exact (normalizedDensity_support ν hu hs X y hh).symm
  rw [unitBallLaw, withDensity_smul_measure, ← withDensity_indicator Metric.isClosed_closedBall.measurableSet, he,
    ← withDensity_smul_measure]
  exact normalizedDensity_is_density ν X hac

end

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.normalizedDensity_unitBall := @_root_.OAI.ProjectionMoments.normalizedDensity_unitBall
