-- Prove2me | solution 2 for OAI.ProjectionMoments.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:42:56.740882+00:00
-- url     : https://prove2.me/submissions/384d958a-8951-4217-95a0-5287b3d408c7

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Main.lean:L14-L26
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ProjectionMoments.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ProjectionMoments_main) verbatim and is proved by it.
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
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel
import Definitions.Def_OAI_Probability_ProjectionMoments_Seeded
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereWeights
import Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_cap_finite_to_asymptotic
import Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_exists_equivalent_tape
import Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_subquadratic_memory
import Theorems.Thm_OAI_NoiselessRegression_Learner_cap_fixed_stop
import Theorems.Thm_OAI_NoiselessRegression_Learner_haar_success
import Theorems.Thm_OAI_NoiselessRegression_Learner_riesz_success
import Theorems.Thm_OAI_NoiselessRegression_fixed_quadratic_memory
import Theorems.Thm_OAI_ProjectionMoments_ballAverage_eq
import Theorems.Thm_OAI_ProjectionMoments_capReference_sum_le_one
import Theorems.Thm_OAI_ProjectionMoments_gaussian_fixed_offset
import Theorems.Thm_OAI_ProjectionMoments_integrated_frame_moment
import Theorems.Thm_OAI_ProjectionMoments_lintegral_polarRows_eq_frame
import Theorems.Thm_OAI_ProjectionMoments_lowerDensity_is_density
import Theorems.Thm_OAI_ProjectionMoments_normalized_unitBall_moment
import Theorems.Thm_OAI_ProjectionMoments_one_block_all_radii
import Theorems.Thm_OAI_ProjectionMoments_positive_cap_domination
import Theorems.Thm_OAI_ProjectionMoments_rieszPotential_ball_control
import Theorems.Thm_OAI_ProjectionMoments_rieszPotential_finite
import Theorems.Thm_OAI_ProjectionMoments_rows_factor
import Theorems.Thm_OAI_ProjectionMoments_sphere_frame_ac

-- ---- from OAI.Probability.GaussianRegression.Execution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
Finite-state sequential execution and terminal-state witnesses.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

lemma run_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    (n : ℕ) (hn : n ≤ T) :
    (L.run s ω x n = .inl (L.forcedRun s ω x n)) ∨
      ∃ t ≤ n, L.run s ω x n = .inr (t, L.forcedRun s ω x t) := by
  induction n with
  | zero =>
    simp only [run, start, forcedRun]
    split
    · exact Or.inr ⟨0, le_rfl, rfl⟩
    · exact Or.inl rfl
  | succ n ih =>
    rcases ih (by omega) with h | ⟨t,ht,h⟩
    · have hnt : n < T := by omega
      rw [run, h]
      simp only [dite_eq_left hnt, forcedRun]
      split
      · exact Or.inr ⟨n+1, le_rfl, by simp [forcedRun, hnt]⟩
      · exact Or.inl rfl
    · right
      exact ⟨t, by omega, by rw [run, h]⟩

lemma terminal_forced_witness (s : UnitSphere d) (ω : Ω) (x : Samples d T) :
    ∃ t ≤ T, L.terminal s ω x = (t, L.forcedRun s ω x t) := by
  rcases L.run_forced_witness s ω x T le_rfl with h | ⟨t,ht,h⟩
  · exact ⟨T, le_rfl, by simp [terminal, h]⟩
  · exact ⟨t, ht, by simp [terminal, h]⟩

end Learner

end NoiselessRegression

end

end OAI

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

-- ---- from OAI.Probability.ProjectionMoments.GaussianDensity ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

lemma map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map (show Measurable (s.indicator (fun y => f (e.symm y))) from
      (hf.comp e.symm.measurable).indicator hs) e.measurable]
  have he (x : X) : s.indicator (fun y => f (e.symm y)) (e x) =
      (e ⁻¹' s).indicator f x := by
    by_cases hx : e x ∈ s <;> simp [hx]
  simp_rw [he]
  exact (lintegral_indicator (hs.preimage e.measurable) f).symm

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

end Triangular

section CoordinateDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_eq_toLp_coordinateMap [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) :
    (rowMap A : E → Label m) = (WithLp.toLp 2) ∘ coordinateMap A := rfl

lemma coordinateDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    volume.withDensity (fun y => coordinateDensity ν m (A,y)) = ν.map (coordinateMap A) := by
  have hr : ν.map (rowMap A) ≪ (volume : Measure (Label m)) := by
    rw [rowMap_eq_toLp_coordinateMap, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← (PiLp.volume_preserving_toLp (Fin m)).map_eq]
    exact hA.map (by fun_prop)
  have h := congrArg (fun μ : Measure (Label m) => μ.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm)
    (lowerDensity_is_density ν m A hr)
  rw [map_withDensity_equiv _ _ _ (by fun_prop),
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.SphereDensity ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma linearEquiv_preserves_ac {m : ℕ} (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    {μ : Measure (Fin m → ℝ)} (hμ : μ ≪ volume) : μ.map T ≪ volume := by
  exact (T.toHomeomorph.toMeasurableEquiv.measurableEmbedding.absolutelyContinuous_map hμ).trans
    (Measure.LinearMap.quasiMeasurePreserving volume T.toLinearEquiv.toLinearMap
      (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero).absolutelyContinuous

theorem sphere_fullRank_ac [Nontrivial E] {m : ℕ} (hm : m+2 ≤ Module.finrank ℝ E)
    {A : Fin m → E} (hA : LinearIndependent ℝ A) :
    NoiselessRegression.ambientSphereLaw.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
  obtain ⟨u,hu,T,hT,hvol⟩ := rows_factor A hA
  have he : NoiselessRegression.ambientSphereLaw.map (coordinateMap A) =
      (NoiselessRegression.ambientSphereLaw.map (coordinateMap u)).map T := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    exact funext hT
  rw [he]
  exact linearEquiv_preserves_ac T (sphere_frame_ac hm hu)

end ProjectionMoments
end

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

lemma polarRows_law {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {u : Fin k → E} (hu : Orthonormal ℝ u) :
    (Measure.pi (fun _ : Fin k => stdGaussian E)).map (polarRows u) = frameLaw u := by
  apply Measure.ext
  intro s hs
  have hf : Measurable (s.indicator (1 : (Fin k → E) → ℝ≥0∞)) := measurable_const.indicator hs
  rw [← lintegral_indicator_one hs, lintegral_map hf (measurable_polarRows u),
    lintegral_polarRows_eq_frame hk hu _ hf, lintegral_indicator_one hs]

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

lemma rowMap_ac_iff {ν : Measure E} {k : ℕ} (A : Fin k → E) :
    ν.map (rowMap A) ≪ (volume : Measure (Label k)) ↔
      ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  constructor
  · intro h
    have hh := h.map (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm.measurable
    rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k)).map_eq,
      Measure.map_map (by fun_prop) (by fun_prop)] at hh
    exact hh
  · intro h
    rw [rowMap_eq_toLp_coordinateMap, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← (PiLp.volume_preserving_toLp (Fin k)).map_eq]
    exact h.map (by fun_prop)

lemma measurableSet_projection_ac (ν : Measure E) [IsFiniteMeasure ν] (k : ℕ) :
    MeasurableSet {A : Fin k → E | ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))} := by
  have h := Kernel.measurableSet_absolutelyContinuous (projectionKernel ν k)
    (Kernel.const (Fin k → E) (volume : Measure (Fin k → ℝ)).toFinite)
  convert h using 1
  ext A
  exact ⟨fun h => h.trans (absolutelyContinuous_toFinite volume),
    fun h => h.trans (toFinite_absolutelyContinuous volume)⟩

lemma polar_ac_to_frame (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) {u : Fin k → E} (hu : Orthonormal ℝ u)
    (h : ∀ᵐ X ∂Measure.pi (fun _ : Fin k => stdGaussian E),
      ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  rw [← polarRows_law hk hu]
  apply (ae_map_iff (measurable_polarRows u).aemeasurable (measurableSet_projection_ac ν k)).mpr
  filter_upwards [h] with X hX
  exact (rowMap_ac_iff _).mp hX

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphereWeightedRestriction_le [Nontrivial E] {h : E → ℝ≥0∞}
    (h1 : ∀ s, h s ≤ 1) (H : Set E) :
    sphereWeightedRestriction h H ≤ NoiselessRegression.ambientSphereLaw := by
  apply Measure.restrict_le_self.trans
  calc
    _ ≤ NoiselessRegression.ambientSphereLaw.withDensity (1 : E → ℝ≥0∞) :=
      withDensity_mono (Filter.Eventually.of_forall h1)
    _ = _ := withDensity_one

lemma sphereWeightedRestriction_finite [Nontrivial E] {h : E → ℝ≥0∞}
    (h1 : ∀ s, h s ≤ 1) (H : Set E) : IsFiniteMeasure (sphereWeightedRestriction h H) :=
  ⟨(Measure.le_iff.mp (sphereWeightedRestriction_le h1 H) Set.univ MeasurableSet.univ).trans_lt (by simp)⟩

lemma sphereWeightedRestriction_support {h : E → ℝ≥0∞} {H : Set E}
    {z : E} {ρ : ℝ} (hH : H ⊆ Metric.closedBall z ρ) :
    (sphereWeightedRestriction h H).support ⊆ Metric.closedBall z ρ :=
  Measure.support_restrict_subset.trans (fun _ hx =>
    (closure_minimal hH Metric.isClosed_closedBall) hx.1)

theorem riesz_deterministic_offsets :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/8
      let α : ℝ := (d:ℝ)/2
      ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h → (∀ s, h s ≤ 1) →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ ρ : ℝ, 0 < ρ →
      ∀ H : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet H → H ⊆ Metric.closedBall z ρ →
      rieszPotential α h < ∞ ∧
      Measurable (lowerDensity (sphereWeightedRestriction h H) k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), LinearIndependent ℝ A →
        volume.withDensity (fun y => lowerDensity (sphereWeightedRestriction h H) k (A,y)) =
          (sphereWeightedRestriction h H).map (rowMap A)) ∧
      (∀ b : Label k, (∫⁻ A, (lowerDensity (sphereWeightedRestriction h H) k (A,rowMap A z+b))^k
          ∂Measure.pi (fun _ => stdGaussian (EuclideanSpace ℝ (Fin d))))^(1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d) * rieszPotential α h * ENNReal.ofReal (ρ^(α-k))) ∧
      (∀ A y, ‖rowMap A‖*ρ < ‖y-rowMap A z‖ →
        lowerDensity (sphereWeightedRestriction h H) k (A,y) = 0) := by
  refine ⟨128,by norm_num,?_⟩
  intro d hd k α h hh h1 z ρ hρ H hH hHz
  let : NeZero d := ⟨by omega⟩
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkd : k+2 ≤ d := by dsimp [k]; omega
  have hαd : α ≤ d := by dsimp [α]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hmargin : (k:ℝ)+k ≤ α := by
    have hn : 4*k ≤ d := by dsimp [k]; omega
    have hn' : 4*(k:ℝ) ≤ d := by exact_mod_cast hn
    dsimp [α]; linarith
  have hfinite : rieszPotential α h < ∞ := by
    apply rieszPotential_finite hα (m := d/2+1) _ _ h1
    · have hn : d ≤ 2*(d/2+1) := by omega
      have hn' : (d:ℝ) ≤ 2*((d/2+1:ℕ):ℝ) := by exact_mod_cast hn
      dsimp [α]; linarith
    · simp only [finrank_euclideanSpace_fin]; omega
  let μ := sphereWeightedRestriction h H
  let : IsFiniteMeasure μ := sphereWeightedRestriction_finite h1 H
  have hs : μ.support ⊆ Metric.closedBall z ρ := sphereWeightedRestriction_support hHz
  have hball : AllBallMass μ (rieszPotential α h).toReal α := by
    intro c r hr
    apply (Measure.restrict_le_self _).trans
    apply (rieszPotential_ball_control hα hh c hr).trans_eq
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfinite.ne]
  refine ⟨hfinite,measurable_lowerDensity μ k,?_,?_,?_⟩
  · intro A hA
    apply lowerDensity_is_density
    apply (rowMap_ac_iff _).mpr
    exact ((Measure.absolutelyContinuous_of_le (sphereWeightedRestriction_le h1 H)).map
      (show Measurable (coordinateMap A) by fun_prop)).trans (sphere_fullRank_ac (by simpa using hkd) hA)
  · intro b
    have hb := gaussian_fixed_offset hball ENNReal.toReal_nonneg z hρ hs k k (by omega)
      hmargin (by simpa using hαd) b
    simpa only [finrank_euclideanSpace_fin,ENNReal.ofReal_mul (by positivity : 0 ≤ (128:ℝ)^d),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (128:ℝ)^d*(rieszPotential α h).toReal),
      ENNReal.ofReal_toReal hfinite.ne] using hb
  · intro A y hy
    exact lowerDensity_eq_zero_of_far μ k A z ρ y hs hy

end

theorem all_radii_sphere_moment :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : ℕ, 16 ≤ d →
      let k := d/4
      let β : ℝ := (d:ℝ)-1-k
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
      Measurable f → (∀ s, f s ≤ 1) →
      ∀ K : ℝ, 0 ≤ K →
      AllBallMass (NoiselessRegression.ambientSphereLaw.withDensity f) K β →
      ∀ z : EuclideanSpace ℝ (Fin d), ∀ R : ℝ, 0 < R →
      ∀ u : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ u →
      let μ := sphereWeightedRestriction f (Metric.closedBall z R)
      Measurable (coordinateDensity μ k) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        (volume : Measure (Fin k → ℝ)).withDensity (fun y => coordinateDensity μ k (A,y)) =
          μ.map (coordinateMap A)) ∧
      (∀ A : Fin k → EuclideanSpace ℝ (Fin d), Orthonormal ℝ A →
        ∀ y : Fin k → ℝ, R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖ →
          coordinateDensity μ k (A,y) = 0) ∧
      (∫⁻ A, ∫⁻ y : Fin k → ℝ, coordinateDensity μ k (A,y)^k ∂volume ∂frameLaw u) ^ (1/(k:ℝ)) ≤
        ENNReal.ofReal (C^d*(C*Real.sqrt d)^((k:ℝ)*(1-1/(k:ℝ)))*
          K*R^(β-(k:ℝ)*(1-1/(k:ℝ)))) := by
  obtain ⟨C,hC,h⟩ := integrated_frame_moment
  refine ⟨C,hC,?_⟩
  intro d hd k β f hf hf1 K hK hball z R hR u hu μ
  let : NeZero d := ⟨by omega⟩
  let : IsFiniteMeasure μ := sphereWeightedRestriction_finite hf1 _
  have hk : 4 ≤ k := by dsimp [k]; omega
  have h3k : 3*k ≤ d := by dsimp [k]; omega
  have h3kR : 3*(k:ℝ) ≤ d := by exact_mod_cast h3k
  have hkR : (4:ℝ) ≤ k := by exact_mod_cast hk
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβd : β ≤ d := by dsimp [β]; linarith
  have hm : 1 ≤ β-(k:ℝ)-((k:ℝ)-2) := by dsimp [β]; linarith
  have hs : μ.support ⊆ Metric.closedBall z R := sphereWeightedRestriction_support Subset.rfl
  have hball' : AllBallMass μ K β := fun c r hr => (Measure.restrict_le_self _).trans (hball c r hr)
  have hac (A : Fin k → EuclideanSpace ℝ (Fin d)) (hA : Orthonormal ℝ A) :
      μ.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) :=
    ((Measure.absolutelyContinuous_of_le (sphereWeightedRestriction_le hf1 _)).map
      (by fun_prop)).trans (sphere_frame_ac (by simp only [finrank_euclideanSpace_fin]; omega) hA)
  have hframe := h d k k β K R μ z u (by omega) (by omega) (by omega)
    hβ (by exact_mod_cast hβd) hm hK hR hs hball' hu
      (polar_ac_to_frame μ (by simpa only [finrank_euclideanSpace_fin] using (show k ≤ d by omega)) hu
        (Filter.Eventually.of_forall (fun X => (rowMap_ac_iff _).mpr (hac _ (polarRows_orthonormal hu X)))))
  refine ⟨hframe.1,?_,hframe.2.2.1,hframe.2.2.2⟩
  intro A hA
  exact coordinateDensity_is_density μ k A (hac A hA)

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.CapDomination ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

theorem positive_family_cap_domination :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 → ∀ N : ℕ,
      ∀ K : Fin N → (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      (∀ j, Measurable (K j)) → (∀ z, ∑ j, K j z ≤ 1) →
      (∑ j, capReference (K j) c r) ≤ 1 ∧
      ∀ j, ∃ D : CapDictionary c r α, ∃ a : D.I → ℝ,
        (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*(r/D.radius i)^α) ∧
        (∑' i, a i*(r/D.radius i)^α) ≤ Real.exp (C*d)*(capReference (K j) c r).toReal^(1-1/(k:ℝ)) ∧
        (capMeasure c r).withDensity (capKernelValue (K j)) ≤
          Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i)) ∧
        (Measure.sum (fun i => ENNReal.ofReal (a i) • capMeasure (D.center i) (D.radius i))) Set.univ < ∞ := by
  obtain ⟨C,hC,h⟩ := positive_cap_domination
  refine ⟨C,hC,?_⟩
  intro d hd k α c hc r hr hr2 N K hK hKsum
  refine ⟨capReference_sum_le_one K hK hKsum c r,?_⟩
  intro j
  apply h d hd c hc r hr hr2 (K j) (hK j)
  intro z
  exact (Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ j)).trans (hKsum z)

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.BorelRules ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

lemma measurable_countable_select {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    {f : J → X → Y} (hf : ∀ j, Measurable (f j)) {g : X → J} (hg : Measurable g) :
    Measurable (fun x => f (g x) x) :=
  (measurable_from_prod_countable_right (f := fun z : J × X => f z.1 z.2) hf).comp (hg.prodMk measurable_id)

lemma measurable_run (L : Learner d M T Ω) (hL : L.MeasurableRules) (n : ℕ) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.run z.1 z.2.1 z.2.2 n) := by
  classical
  induction n with
  | zero =>
    exact (measurable_of_finite (fun a : Bool × State M =>
      if a.1 then Sum.inr (0,a.2) else Sum.inl a.2)).comp
        (hL.initial.comp (measurable_fst.comp measurable_snd))
  | succ n ih =>
    let F : RunStatus M → (UnitSphere d × (Ω × Samples d T)) → RunStatus M := fun j z =>
      match j with
      | .inr done => .inr done
      | .inl j => if hn : n < T then
          let row := z.2.2 ⟨n,hn⟩
          let a := L.transition (n+1) z.2.1 j (row,⟪row,z.1.val⟫)
          if a.1 then .inr (n+1,a.2) else .inl a.2
        else .inl j
    change Measurable (fun z => F (L.run z.1 z.2.1 z.2.2 n) z)
    apply measurable_countable_select _ ih
    intro j
    cases j with
    | inr done => exact measurable_const
    | inl j =>
      dsimp [F]
      split_ifs with hn
      · exact (measurable_of_finite (fun a : Bool × State M =>
          if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2)).comp
            ((hL.transition (n+1) j).comp (show Measurable (fun z : UnitSphere d × (Ω × Samples d T) =>
              (z.2.1,(z.2.2 ⟨n,hn⟩,⟪z.2.2 ⟨n,hn⟩,z.1.val⟫))) from by fun_prop))
      · exact measurable_const

lemma measurable_terminal (L : Learner d M T Ω) (hL : L.MeasurableRules) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.terminal z.1 z.2.1 z.2.2) := by
  exact (measurable_of_countable (fun j : RunStatus M =>
    match j with | .inl j => (T,j) | .inr done => done)).comp (L.measurable_run hL T)

end Learner

universe u

namespace Learner
variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

end Learner
end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Seeded ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner

section
open Learner
variable {d M T : ℕ}

end

universe u
variable {d M T : ℕ}

lemma seed_average_bound {Ξ : Type u} [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] {f : Ξ → ℝ≥0∞} {C : ℝ≥0∞}
    (h : ∀ᵐ ξ ∂ρ, f ξ ≤ C) : ∫⁻ ξ, f ξ ∂ρ ≤ C := by
  calc
    _ ≤ ∫⁻ _, C ∂ρ := lintegral_mono_ae h
    _ = C := by simp

lemma exists_successful_seed {Ξ : Type u} [MeasurableSpace Ξ] (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] {P : Ξ → Prop} (hP : ∀ᵐ ξ ∂ρ, P ξ)
    {f : Ξ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (hs : c ≤ ∫⁻ ξ, f ξ ∂ρ) :
    ∃ ξ, P ξ ∧ c ≤ f ξ := by
  by_contra h
  have hlt : ∀ᵐ ξ ∂ρ, f ξ < c := by
    filter_upwards [hP] with ξ hξ
    exact lt_of_not_ge (fun hf => h ⟨ξ,hξ,hf⟩)
  have hbound : ∫⁻ ξ, f ξ ∂ρ ≤ c := seed_average_bound ρ (ae_le_of_ae_lt hlt)
  have hstrict := lintegral_strict_mono (show ρ ≠ 0 from by
    intro he; have hh := measure_univ (μ := ρ); rw [he] at hh; simp at hh)
    (aemeasurable_const (b := c)) (ne_top_of_le_ne_top hc hbound) hlt
  have hh : ∫⁻ ξ, f ξ ∂ρ < c := by simpa using hstrict
  exact not_lt_of_ge hs hh

theorem riesz_success :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let q := d/8
      let W : ℝ := ((T:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C₀^d*ε^((d:ℝ)/2-1)*(1+C₀^d*(1+Real.log (1/ε))*W^(1/(q:ℝ)))^((T+q-1)/q)) := by
  obtain ⟨C,hC,h⟩ := Learner.riesz_success.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK q W
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε]
  exact h d M T hd ε hε hε10 (Tape M T) ν hν L hL

theorem haar_success :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d M T : ℕ, 16 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let k := d/4
      let Nstar : ℝ := ((k:ℝ)+2)*2^M
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (C^d*ε^k*(C^d*Nstar^(1/(k:ℝ)))^((T+k-1)/k)) := by
  obtain ⟨C,hC,h⟩ := Learner.haar_success.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK k Nstar
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε]
  exact h d M T hd ε hε hε10 (Tape M T) ν hν L hL

theorem cap_fixed_stop :
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededFixedSuccess K ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((t+k-1)/k)) := by
  obtain ⟨C,hC,h⟩ := Learner.cap_fixed_stop.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK t ht k α
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,_,he⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε t]
  exact h d M T hd ε hε hε10 (Tape M T) ν hν L hL
    (L.measurable_terminal hB).fst.aemeasurable t ht

theorem fixed_quadratic_memory : FixedQuadraticMemory.{u} := by
  intro A hA
  obtain ⟨c,hc,d₀,h⟩ := NoiselessRegression.fixed_quadratic_memory.{0} A hA
  refine ⟨c,hc,max d₀ 3,?_⟩
  intro d hd M T hM ε hε hε10 Ξ _ ρ hρ K hK hs
  let : IsProbabilityMeasure ρ := hρ
  obtain ⟨ξ,hξ,hsξ⟩ := exists_successful_seed ρ hK (ENNReal.div_ne_top (by norm_num) (by norm_num) : (2/3 : ℝ≥0∞) ≠ ∞) hs
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  apply h d (by omega) M T hM ε hε hε10 (Tape M T) ν hν L hL
  rwa [he ε]

end FiniteKernelLearner

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Asymptotics ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace Learner
variable {d M T : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma uniformSuccess_le_sum_fixed (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) :
    L.uniformSuccess ρ ε ≤ ∑ t : Fin (T+1), L.uniformFixedSuccess ρ ε t := by
  classical
  let μ := (uniformSphere d).prod (ρ.prod (sampleLaw d T))
  have hs : {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε} =
      ⋃ t : Fin (T+1), {z | (L.terminal z.1 z.2.1 z.2.2).1 = t ∧
        angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro hz
      obtain ⟨t,ht,he⟩ := L.terminal_forced_witness z.1 z.2.1 z.2.2
      exact ⟨⟨t,by omega⟩,by simpa [he] using hz⟩
    · rintro ⟨t,ht,hz⟩
      exact hz
  change μ _ ≤ ∑ t : Fin (T+1), μ _
  rw [hs]
  exact (measure_iUnion_le _).trans_eq (tsum_fintype _)

end Learner
namespace FiniteKernelLearner

section
universe u

theorem cap_total_success :
    ∃ C : ℝ, 0 < C ∧ ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d M T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (((T:ℝ)+1)*Real.exp (C*d)*(ε/2)^α*
          (Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((T+k-1)/k)) := by
  obtain ⟨C,hC,h⟩ := Learner.cap_fixed_stop.{0}
  refine ⟨C,hC,?_⟩
  intro d M T hd ε hε hε10 Ξ _ ρ hρ K hK k α
  let : IsProbabilityMeasure ρ := hρ
  apply seed_average_bound
  filter_upwards [hK] with ξ hξ
  obtain ⟨ν,L,hν,hB,hL,he,_⟩ := (K ξ).exists_equivalent_tape hξ (by omega)
  rw [←he ε]
  have hs := L.uniformSuccess_le_sum_fixed ν ε
  have hbase : 1 ≤ Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity))
      (Real.one_le_rpow (by norm_num) (by positivity))
  apply hs.trans
  calc
    _ ≤ ∑ _t : Fin (T+1), ENNReal.ofReal
        (Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/k))^((T+k-1)/k)) := by
      apply Finset.sum_le_sum
      intro t _
      apply (h d M T hd ε hε hε10 (Tape M T) ν hν L hL
        (L.measurable_terminal hB).fst.aemeasurable t (by omega)).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_right₀ hbase (Nat.div_le_div_right (by omega))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
      rw [nsmul_eq_mul, ←ENNReal.ofReal_natCast,
        ←ENNReal.ofReal_mul (by positivity : 0 ≤ ((T+1:ℕ):ℝ))]
      congr 1
      push_cast
      ring

end

section

universe u
variable {d M T : ℕ} {Ξ : Type u} [MeasurableSpace Ξ]

lemma seededSuccess_eq_integral_pointwise [NeZero d]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) [SFinite ρ] (ε : ℝ)
    (hm : JointSuccessMeasurable K ρ ε) :
    seededSuccess K ρ ε = ∫⁻ s, seededPointwiseSuccess K ρ ε s ∂uniformSphere d := by
  let f := fun z : UnitSphere d × (Ξ × Samples d T) =>
    (K z.2.1).conditionalSuccess ε z.1 z.2.2
  let e : ((UnitSphere d × Samples d T) × Ξ) ≃ᵐ UnitSphere d × (Ξ × Samples d T) :=
    MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.prodComm))
  have hp : MeasurePreserving e (((uniformSphere d).prod (sampleLaw d T)).prod ρ)
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
      (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  have hf : AEMeasurable f ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := hm
  have hfD : AEMeasurable (fun z : (UnitSphere d × Samples d T) × Ξ => f (e z))
      (((uniformSphere d).prod (sampleLaw d T)).prod ρ) :=
    hf.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  calc
    _ = ∫⁻ ξ, ∫⁻ z : UnitSphere d × Samples d T, f (z.1,(ξ,z.2))
          ∂((uniformSphere d).prod (sampleLaw d T)) ∂ρ := rfl
    _ = ∫⁻ z : UnitSphere d × Samples d T, ∫⁻ ξ, f (z.1,(ξ,z.2)) ∂ρ
          ∂((uniformSphere d).prod (sampleLaw d T)) := (lintegral_lintegral_swap hfD).symm
    _ = ∫⁻ z, f (e z) ∂(((uniformSphere d).prod (sampleLaw d T)).prod ρ) :=
      (lintegral_prod _ hfD).symm
    _ = ∫⁻ z, f z ∂((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
      hp.lintegral_comp_emb e.measurableEmbedding f
    _ = _ := lintegral_prod _ hf

lemma seededSuccess_of_pointwise [NeZero d]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) [SFinite ρ] (ε : ℝ)
    (hm : JointSuccessMeasurable K ρ ε)
    (hs : ∀ s, (2/3 : ℝ≥0∞) ≤ seededPointwiseSuccess K ρ ε s) :
    (2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε := by
  rw [seededSuccess_eq_integral_pointwise K ρ ε hm]
  calc
    _ = ∫⁻ _ : UnitSphere d, (2/3 : ℝ≥0∞) ∂uniformSphere d := by simp
    _ ≤ _ := lintegral_mono hs

theorem subquadratic_memory_with_pointwise : SubquadraticMemoryWithPointwise.{u} := by
  obtain ⟨c,hc,h⟩ := subquadratic_memory.{u}
  refine ⟨c,hc,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := h M hM
  refine ⟨max d₀ 1,?_⟩
  intro d hd T ε hε hε10 Ξ _ ρ hρ K hK hs
  let : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  apply hd₀ d (by omega) T ε hε hε10 Ξ ρ hρ K hK
  rcases hs with hs | ⟨hm,hs⟩
  · exact hs
  · exact seededSuccess_of_pointwise K ρ ε hm hs

end

universe u

theorem cap_fixed_stop_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun d => (M d:ℝ)) (fun d => (d:ℝ)^2) →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      ∀ t : ℕ, t ≤ T →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      seededFixedSuccess K ρ ε t ≤ ENNReal.ofReal
        (Real.exp (C*d*(1+((t+k-1)/k:ℕ)))*(ε/2)^α) := by
  obtain ⟨C,hC,h⟩ := cap_fixed_stop.{u}
  refine ⟨C+32,by linarith,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max d₀ 32,?_⟩
  intro d hd T ε hε hε10 Ξ _ ρ hρ K hK t ht k α
  have hm : (M d:ℝ) ≤ (d:ℝ)^2 := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (M d)),
      abs_of_nonneg (sq_nonneg (d:ℝ))] using hd₀ d (by omega)
  exact (h d (M d) T (by omega) ε hε hε10 Ξ ρ hρ K hK t ht).trans
    (ENNReal.ofReal_le_ofReal (cap_finite_to_asymptotic C (by omega) hm ε α _ hε.le))

lemma cap_ceil_cost {d T : ℕ} (hd : 32 ≤ d) :
    (d:ℝ)*(1+((T+d/16-1)/(d/16):ℕ)) ≤ 2*d+32*T := by
  let k := d/16
  let n := (T+k-1)/k
  have hk : 0 < k := by dsimp [k]; omega
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hdiv : n*k ≤ T+k := (Nat.div_mul_le_self _ _).trans (by omega)
  have hdivR : (n:ℝ)*k ≤ (T:ℝ)+k := by exact_mod_cast hdiv
  have hdR : (d:ℝ) ≤ 32*k := by exact_mod_cast (show d ≤ 32*k by dsimp [k]; omega)
  have hn : (n:ℝ) ≤ (T:ℝ)/k+1 := by
    have he := div_mul_cancel₀ (T:ℝ) hkR.ne'
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α := ℝ) d)
  have hdk : (d:ℝ)/(k:ℝ) ≤ 32 := (div_le_iff₀ hkR).mpr hdR
  have hT := mul_le_mul_of_nonneg_right hdk (Nat.cast_nonneg (α := ℝ) T)
  change (d:ℝ)*(1+(n:ℝ)) ≤ _
  calc
    _ ≤ (d:ℝ)*((T:ℝ)/k+2) := by nlinarith
    _ = (d:ℝ)/k*T+2*d := by ring
    _ ≤ _ := by linarith

lemma cap_accuracy_cost {d : ℕ} (hd : 3 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (ε/2)^(((d:ℝ)-1)/2) ≤ Real.exp (-(d:ℝ)*Real.log (1/ε)/3) := by
  have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 ≤ ((d:ℝ)-1)/2 := by linarith
  calc
    _ ≤ ε^(((d:ℝ)-1)/2) := Real.rpow_le_rpow (by positivity) (by linarith) ha
    _ ≤ ε^((d:ℝ)/3) := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
    _ = _ := by
      rw [Real.rpow_def_of_pos hε,one_div,Real.log_inv]
      congr 1
      ring

theorem cap_total_success_asymptotic :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ M : ℕ → ℕ,
      Asymptotics.IsLittleO atTop (fun d => (M d:ℝ)) (fun d => (d:ℝ)^2) →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
      0 < ε → ε ≤ 1/10 →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (ρ : Measure Ξ), IsProbabilityMeasure ρ →
      ∀ K : Ξ → FiniteKernelLearner d (M d) T, (∀ᵐ ξ ∂ρ, (K ξ).CompletedRules) →
      seededSuccess K ρ ε ≤ ENNReal.ofReal
        (((T:ℝ)+1)*Real.exp (C₁*d+C₂*T-(d:ℝ)*Real.log (1/ε)/3)) := by
  obtain ⟨C,hC,h⟩ := cap_total_success.{u}
  refine ⟨2*(C+32),32*(C+32),by positivity,by positivity,?_⟩
  intro M hM
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max d₀ 32,?_⟩
  intro d hd T ε hε hε10 Ξ _ ρ hρ K hK
  have hm : (M d:ℝ) ≤ (d:ℝ)^2 := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (M d)),
      abs_of_nonneg (sq_nonneg (d:ℝ))] using hd₀ d (by omega)
  apply (h d (M d) T (by omega) ε hε hε10 Ξ ρ hρ K hK).trans
  apply ENNReal.ofReal_le_ofReal
  simp only [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (T:ℝ)+1)
  have hfinite := cap_finite_to_asymptotic C (by omega) hm ε (((d:ℝ)-1)/2)
    ((T+d/16-1)/(d/16)) hε.le
  simp only [mul_assoc] at hfinite
  apply hfinite.trans
  have hcost := mul_le_mul_of_nonneg_left (cap_ceil_cost (T := T) (by omega : 32 ≤ d))
    (by positivity : (0:ℝ) ≤ C+32)
  have he : Real.exp ((C+32)*d*(1+((T+d/16-1)/(d/16):ℕ))) ≤
      Real.exp (2*(C+32)*d+32*(C+32)*T) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simp only [mul_assoc] at he
  apply (mul_le_mul he (cap_accuracy_cost (d := d) (by omega) hε (by linarith)) (by positivity) (by positivity)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

end FiniteKernelLearner
end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Main ----
namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open NoiselessRegression NoiselessRegression.FiniteKernelLearner
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace ProjectionMoments

theorem main : MainStatement.{u} := by
  refine ⟨integrated_frame_moment, normalized_unitBall_moment, all_radii_sphere_moment,
    positive_family_cap_domination, riesz_deterministic_offsets, one_block_all_radii,
    NoiselessRegression.FiniteKernelLearner.haar_success,
    NoiselessRegression.FiniteKernelLearner.riesz_success,
    NoiselessRegression.FiniteKernelLearner.cap_fixed_stop,
    NoiselessRegression.FiniteKernelLearner.cap_total_success,
    NoiselessRegression.FiniteKernelLearner.cap_fixed_stop_asymptotic,
    NoiselessRegression.FiniteKernelLearner.cap_total_success_asymptotic, ?_,
    NoiselessRegression.FiniteKernelLearner.subquadratic_memory_with_pointwise,
    NoiselessRegression.FiniteKernelLearner.fixed_quadratic_memory⟩
  intro d M T hd K hK
  exact K.exists_equivalent_tape hK hd

end ProjectionMoments

end

end

end OAI

-- ---- mission target ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
universe u
open NoiselessRegression NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace OAI
namespace ProjectionMoments
theorem _root_.solution : MainStatement.{u} := by
  first
    | exact OAI.ProjectionMoments.main
    | (apply OAI.ProjectionMoments.main <;> assumption)
    | (intros; apply OAI.ProjectionMoments.main <;> assumption)
end ProjectionMoments
end OAI
