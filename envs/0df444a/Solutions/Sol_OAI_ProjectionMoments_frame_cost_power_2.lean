-- Prove2me | solution 2 for OAI.ProjectionMoments.frame_cost_power
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:33:39.1314+00:00
-- url     : https://prove2.me/submissions/5f0d4b3b-110b-4262-ab76-647b74043d26

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/FrameMoments.lean:L149-L202
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.frame_cost_power. The node keeps its source
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

-- ---- from OAI.Probability.ProjectionMoments.FrameMoments ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_ballAverage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

lemma frame_cost_power {d m n : ℕ} (hd : 1 ≤ d) (hm : m ≤ d)
    (a K R : ℝ) (hK : 0 ≤ K) (hR : 0 < R) :
    (2 : ℝ)^m * (Real.sqrt (2*d))^(m*n) *
      ((K*R^(a-m))^(n+1) * R^m * (128 : ℝ)^(d*n)) ≤
      ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
        R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))))^(n+1) := by
  have hq : (n : ℝ)+1 ≠ 0 := by positivity
  have hexp : ((m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1) = (m*n:ℕ) := by
    push_cast
    field_simp
    ring
  have hRexp : (a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1) =
      (a-m)*((n:ℝ)+1)+m := by
    field_simp
    ring
  have hscale : (K*R^(a-m))^(n+1)*R^m =
      K^(n+1)*R^((a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1)) := by
    rw [mul_pow, mul_assoc, ← Real.rpow_mul_natCast hR.le,
      ← Real.rpow_natCast R m, ← Real.rpow_add hR]
    congr 2
    rw [Nat.cast_add, Nat.cast_one, hRexp]
  have h2 : (2 : ℝ)^m ≤ 256^d := by
    apply (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 256) m).trans
    exact pow_le_pow_right₀ (by norm_num) hm
  have h128 : (128 : ℝ)^(d*n) ≤ 256^(d*n) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) (d*n)
  have hcoef : (2 : ℝ)^m * 128^(d*n) ≤ 256^(d*(n+1)) := by
    apply (mul_le_mul h2 h128 (by positivity) (by positivity)).trans_eq
    rw [← pow_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (2*d) ≤ 256*Real.sqrt d := by
    rw [Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  have hS : ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
      R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))))^(n+1) =
      256^(d*(n+1)) * (256*Real.sqrt d)^(m*n) *
        (K^(n+1)*R^((a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1))) := by
    simp only [mul_pow]
    rw [← pow_mul, ← Real.rpow_mul_natCast (by positivity),
      ← Real.rpow_mul_natCast hR.le]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hexp, Real.rpow_natCast]
    ring
  rw [hS]
  calc
    _ = (2^m*128^(d*n))*(Real.sqrt (2*d))^(m*n) *
        (K^(n+1)*R^((a-(m:ℝ)*(1-1/((n:ℝ)+1)))*((n:ℝ)+1))) := by
      rw [← hscale]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hcoef (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt (m*n))
        (by positivity) (by positivity)) (by positivity)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.frame_cost_power := @_root_.OAI.ProjectionMoments.frame_cost_power
