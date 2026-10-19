-- Prove2me | solution 2 for OAI.ProjectionMoments.normalized_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:48:52.404245+00:00
-- url     : https://prove2.me/submissions/d4dae082-1113-48fa-a2cc-bcceea32bd79

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/BallMoments.lean:L241-L289
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.normalized_cost. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionMoments_unit_ball_volume_bound

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

lemma unitBallVolume_bound (k : ℕ) (hk : 1 ≤ k) :
    unitBallVolume k ≤ ENNReal.ofReal ((6/Real.sqrt k)^k) := by
  rw [unitBallVolume, Measure.addHaar_unitClosedBall_eq_addHaar_unitBall]
  exact unit_ball_volume_bound k hk

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

lemma normalized_cost (d k n : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (hdk : d ≤ 32*k)
    (D : ℝ) (hD : 0 < D) :
    unitBallVolume k ^ n *
      ((2 : ℝ≥0∞)^k * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) *
        (ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n))) ≤
      ENNReal.ofReal ((16384 * max D 1)^(d*(n+1))) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hdR : (d:ℝ) ≤ 32*k := by exact_mod_cast hdk
  have hroot : Real.sqrt (2*d) ≤ 8*Real.sqrt k := by
    have h1 := Real.sq_sqrt (show (0:ℝ) ≤ 2*d by positivity)
    have h2 := Real.sq_sqrt hkR.le
    have h3 := Real.sqrt_nonneg (2*(d:ℝ))
    have h4 := Real.sqrt_pos.mpr hkR
    nlinarith
  have hc : 0 ≤ 6/Real.sqrt k := by positivity
  have hcs : 6/Real.sqrt k * Real.sqrt (2*d) ≤ 48 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (Real.sqrt_pos.mpr hkR)]
    nlinarith
  have hvol : unitBallVolume k ^ n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) ≤
      (48 : ℝ≥0∞)^(k*n) := by
    calc
      _ ≤ ENNReal.ofReal ((6/Real.sqrt k)^k)^n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n) :=
        mul_le_mul' (pow_le_pow_left' (unitBallVolume_bound k hk) n) le_rfl
      _ = ENNReal.ofReal (6/Real.sqrt k * Real.sqrt (2*d))^(k*n) := by
        rw [ENNReal.ofReal_pow hc, ← pow_mul, ENNReal.ofReal_mul hc, mul_pow]
      _ ≤ (48 : ℝ≥0∞)^(k*n) := pow_le_pow_left' (by exact_mod_cast ENNReal.ofReal_le_ofReal hcs) _
  have h2 : (2 : ℝ≥0∞)^k ≤ (2 : ℝ≥0∞)^(d*(n+1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have h48 : (48 : ℝ≥0∞)^(k*n) ≤ (64 : ℝ≥0∞)^(d*(n+1)) :=
    (pow_le_pow_left' (by norm_num : (48:ℝ≥0∞) ≤ 64) _).trans
      (pow_le_pow_right₀ (by norm_num) (by nlinarith))
  have h128 : (128 : ℝ≥0∞)^(d*n) ≤ (128 : ℝ≥0∞)^(d*(n+1)) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hDD : ENNReal.ofReal (D^d)^(n+1) ≤ ENNReal.ofReal (max D 1)^(d*(n+1)) := by
    rw [ENNReal.ofReal_pow hD.le, ← pow_mul]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  calc
    _ = (2 : ℝ≥0∞)^k *
        (unitBallVolume k ^ n * ENNReal.ofReal (Real.sqrt (2*d))^(k*n)) *
        ENNReal.ofReal (D^d)^(n+1) * (128 : ℝ≥0∞)^(d*n) := by ring
    _ ≤ (2 : ℝ≥0∞)^(d*(n+1)) * (64 : ℝ≥0∞)^(d*(n+1)) *
        ENNReal.ofReal (max D 1)^(d*(n+1)) * (128 : ℝ≥0∞)^(d*(n+1)) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' h2 (hvol.trans h48)) hDD) h128
    _ = ENNReal.ofReal ((16384 * max D 1)^(d*(n+1))) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
      norm_num only [ENNReal.ofReal_ofNat]
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      congr 1
      ring

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.normalized_cost := @_root_.OAI.ProjectionMoments.normalized_cost
