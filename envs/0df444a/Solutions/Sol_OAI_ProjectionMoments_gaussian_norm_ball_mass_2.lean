-- Prove2me | solution 2 for OAI.ProjectionMoments.gaussian_norm_ball_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:19:34.21308+00:00
-- url     : https://prove2.me/submissions/30366b1c-896d-4016-a007-10fa2574bddd

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/GaussianDensity.lean:L102-L130
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.gaussian_norm_ball_mass. The node keeps its source
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

-- ---- from OAI.Probability.ProjectionMoments.GaussianDensity ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lintegral_gaussianReal_sq :
    ∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂gaussianReal 0 1 = 1 := by
  have hi : Integrable (fun x : ℝ => x^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => sq_nonneg x))]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hv
  simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one, ENNReal.ofReal_one] using
    congrArg ENNReal.ofReal hv

lemma lintegral_stdGaussian_norm_sq :
    ∫⁻ x : E, ENNReal.ofReal (‖x‖^2) ∂stdGaussian E = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, lintegral_map (by fun_prop) (by fun_prop)]
  have he (x : Fin (Module.finrank ℝ E) → ℝ) :
      ‖∑ i, x i • b i‖^2 = ∑ i, (x i)^2 := by
    rw [b.sum_repr_symm (WithLp.toLp 2 x), LinearIsometryEquiv.norm_map]
    exact EuclideanSpace.real_norm_sq_eq _
  simp_rw [he, ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
  have hi (i : Fin (Module.finrank ℝ E)) :
      ∫⁻ x : Fin (Module.finrank ℝ E) → ℝ, ENNReal.ofReal (x i ^ 2)
        ∂Measure.pi (fun _ => gaussianReal 0 1) = 1 := by
    rw [← lintegral_gaussianReal_sq]
    exact (measurePreserving_eval (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) i).lintegral_comp
      (show Measurable (fun x : ℝ => ENNReal.ofReal (x^2)) by fun_prop)
  simp_rw [hi]
  simp

lemma gaussian_norm_ball_mass (hd : 0 < Module.finrank ℝ E) :
    (2 : ℝ≥0∞)⁻¹ ≤ stdGaussian E (Metric.closedBall 0 (Real.sqrt (2 * Module.finrank ℝ E))) := by
  let d : ℝ := Module.finrank ℝ E
  have hd' : 0 < d := by dsimp [d]; exact_mod_cast hd
  have hneg : stdGaussian E {x | ENNReal.ofReal (2*d) ≤ ENNReal.ofReal (‖x‖^2)} ≤ (2 : ℝ≥0∞)⁻¹ := by
    have h := meas_ge_le_lintegral_div (μ := stdGaussian E)
      (f := fun x => ENNReal.ofReal (‖x‖^2)) (by fun_prop)
      (ε := ENNReal.ofReal (2*d)) (by positivity) ENNReal.ofReal_ne_top
    rw [lintegral_stdGaussian_norm_sq] at h
    convert h using 1
    have hd0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat, d,
      ENNReal.ofReal_natCast, div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_left_comm, ENNReal.mul_inv_cancel hd0 (by simp), mul_one]
  have hsub : (Metric.closedBall (0 : E) (Real.sqrt (2*d)))ᶜ ⊆
      {x | ENNReal.ofReal (2*d) ≤ ENNReal.ofReal (‖x‖^2)} := by
    intro x hx
    have hx' : Real.sqrt (2*d) < ‖x‖ := by simpa only [mem_compl_iff, Metric.mem_closedBall,
      dist_zero_right, not_le] using hx
    apply ENNReal.ofReal_le_ofReal
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (2*d)) (norm_nonneg x)).mpr hx'.le
    rwa [Real.sq_sqrt (by positivity)] at hsq
  have hc := (measure_mono hsub).trans hneg
  rw [measure_compl measurableSet_closedBall (measure_ne_top _ _), measure_univ] at hc
  change (2 : ℝ≥0∞)⁻¹ ≤ stdGaussian E (Metric.closedBall 0 (Real.sqrt (2*d)))
  have := tsub_le_iff_left.mp hc
  have he : (1 : ℝ≥0∞) - (2 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by norm_num
  rw [← he]
  exact tsub_le_iff_right.mpr this

end

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.gaussian_norm_ball_mass := @_root_.OAI.ProjectionMoments.gaussian_norm_ball_mass
