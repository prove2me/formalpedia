-- Prove2me | solution 2 for OAI.ProjectionMoments.unit_ball_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:45:09.31418+00:00
-- url     : https://prove2.me/submissions/a05917c9-f5c0-4daa-a8b8-3c7ea320406a

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Polar.lean:L227-L277
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.unit_ball_volume_bound. The node keeps its source
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
end GramFactorization

section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
variable [MeasurableSpace E] [BorelSpace E]
end GramDistances

variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma lintegral_pi_snoc (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => ν) =
      ∫⁻ v : Fin n → E, ∫⁻ x, f (Fin.snoc v x) ∂ν ∂Measure.pi (fun _ => ν) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f,
    lintegral_prod_symm]
  · congr 1
    ext v
    congr 1
    ext x
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact Fin.insertNth_last' x v
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.GaussianKernel ----
namespace OAI

/-!
Gaussian coordinate domination and replica kernel bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianDomination

section ReplicaKernel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma lintegral_fin_prod (n : ℕ) (f : Fin n → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → X, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ) =
      ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lintegral_pi_snoc μ _ (by fun_prop)]
    simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    simp_rw [lintegral_const_mul _ (hf (Fin.last n))]
    rw [lintegral_mul_const _ (by fun_prop), ih _ (fun i => hf i.castSucc)]

end ReplicaKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Polar ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

end

lemma euclidean_gaussian_integral (k : ℕ) :
    (∫⁻ x : Fin k → ℝ, ENNReal.ofReal (Real.exp (-‖WithLp.toLp 2 x‖^2)) ∂volume) =
      ENNReal.ofReal (Real.sqrt Real.pi ^ k) := by
  have hex (x : Fin k → ℝ) : Real.exp (-‖WithLp.toLp 2 x‖^2) =
      ∏ i, Real.exp (-(x i)^2) := by
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_neg_distrib, Real.exp_sum]
    congr 1
    funext i
    simp only [Real.norm_eq_abs, sq_abs]
  have hscalar : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x^2)) ∂volume) =
      ENNReal.ofReal (Real.sqrt Real.pi) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · simpa using congrArg ENNReal.ofReal (integral_gaussian 1)
    · simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
    · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
  simp_rw [hex, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  rw [volume_pi, NoiselessRegression.lintegral_fin_prod (volume : Measure ℝ) k
    (fun _ x => ENNReal.ofReal (Real.exp (-x^2))) (fun _ => by fun_prop)]
  simp only [hscalar, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (Real.sqrt_nonneg _)]

lemma unit_ball_volume_bound (k : ℕ) (hk : 1 ≤ k) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1) ≤
      ENNReal.ofReal ((6 / Real.sqrt k)^k) := by
  let r := Real.sqrt (k : ℝ)
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hr : 0 < r := Real.sqrt_pos.mpr hk0
  have hr2 : r^2 = k := Real.sq_sqrt hk0.le
  have hlower : ENNReal.ofReal (Real.exp (-(k:ℝ))) *
      (volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 r) ≤
      ENNReal.ofReal (Real.sqrt Real.pi ^ k) := by
    calc
      _ = ∫⁻ _x in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r,
          ENNReal.ofReal (Real.exp (-(k:ℝ))) ∂volume := by simp
      _ ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r,
          ENNReal.ofReal (Real.exp (-‖x‖^2)) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hx' : ‖x‖ ≤ r := by simpa [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp hx).le
        nlinarith [norm_nonneg x]
      _ ≤ ∫⁻ x : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (Real.exp (-‖x‖^2)) ∂volume :=
        setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (Real.sqrt Real.pi ^ k) := by
        rw [← (PiLp.volume_preserving_toLp (Fin k)).map_eq,
          lintegral_map (by fun_prop) (by fun_prop)]
        exact euclidean_gaussian_integral k
  rw [Measure.addHaar_ball_of_pos volume 0 hr, finrank_euclideanSpace_fin] at hlower
  have h := ENNReal.toReal_le_of_le_ofReal (by positivity) hlower
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)] at h
  have hexp : Real.exp (-(k:ℝ)) * Real.exp (k:ℝ) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 ≤ ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal :=
    ENNReal.toReal_nonneg
  have hnum : Real.exp (k:ℝ) * Real.sqrt Real.pi ^ k ≤ (6:ℝ)^k := by
    rw [show (k:ℝ) = (k:ℝ)*1 by ring, Real.exp_nat_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hs : Real.sqrt Real.pi < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith [Real.pi_lt_four])
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1, Real.sqrt_nonneg Real.pi]
  have hv : ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal ≤
      (6/r)^k := by
    rw [div_pow, le_div_iff₀ (pow_pos hr _)]
    calc
      _ = Real.exp (k:ℝ)*(Real.exp (-(k:ℝ))*r^k*
          ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal) := by
          nlinarith [congrArg (fun t : ℝ => t * (r^k *
            ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal)) hexp]
      _ ≤ Real.exp (k:ℝ)*Real.sqrt Real.pi^k := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (Real.exp_pos (k:ℝ)).le
      _ ≤ _ := hnum
  exact (ENNReal.le_ofReal_iff_toReal_le measure_ball_lt_top.ne (by positivity)).mpr hv

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.unit_ball_volume_bound := @_root_.OAI.ProjectionMoments.unit_ball_volume_bound
