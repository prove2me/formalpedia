-- Prove2me | solution 1 for OAI.ProjectionMoments.frame_cost_power
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:14:13.569089+00:00
-- url     : https://prove2.me/submissions/9a6e1777-988f-4aec-a475-199f0ac130f5

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

open OAI OAI.ProjectionMoments
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
theorem solution {d m n : ℕ} (hd : 1 ≤ d) (hm : m ≤ d)
    (a K R : ℝ) (hK : 0 ≤ K) (hR : 0 < R) :
    (2 : ℝ)^m * (Real.sqrt (2*d))^(m*n) *
      ((K*R^(a-m))^(n+1) * R^m * (128 : ℝ)^(d*n)) ≤
      ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
        R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))))^(n+1) := by
  set x : ℝ := (m:ℝ)*(1-1/((n:ℝ)+1))
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hx : x * ((n:ℝ)+1) = ((m*n : ℕ) : ℝ) := by
    simp only [x]; push_cast; field_simp; ring
  have hB : (0:ℝ) ≤ 256 * Real.sqrt d := by positivity
  have hRR : ((256 : ℝ)^d * (256*Real.sqrt d)^x * K * R^(a-x))^(n+1) =
      ((256:ℝ)^d)^(n+1) * (256 * Real.sqrt d)^(m*n) * (K^(n+1) * R^((a-x)*((n:ℝ)+1))) := by
    rw [mul_pow, mul_pow, mul_pow, ← Real.rpow_mul_natCast hB, ← Real.rpow_mul_natCast hR.le]
    push_cast
    rw [hx, Real.rpow_natCast]
    push_cast; ring
  have hL : (2 : ℝ)^m * (Real.sqrt (2*d))^(m*n) * ((K*R^(a-m))^(n+1) * R^m * (128 : ℝ)^(d*n)) =
      (2 : ℝ)^m * (Real.sqrt (2*d))^(m*n) * (128 : ℝ)^(d*n) * (K^(n+1) * R^((a-x)*((n:ℝ)+1))) := by
    have hE : (a - x) * ((n:ℝ)+1) = (a - m) * ((n:ℝ)+1) + m := by
      have : x * ((n:ℝ)+1) = m * n := by rw [hx]; push_cast; ring
      nlinarith
    rw [hE, Real.rpow_add hR, Real.rpow_natCast, mul_pow, ← Real.rpow_mul_natCast hR.le]
    push_cast; ring
  rw [hRR, hL]
  have hKR : 0 ≤ K^(n+1) * R^((a-x)*((n:ℝ)+1)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hKR
  have hs : Real.sqrt (2 * d) = Real.sqrt 2 * Real.sqrt d := Real.sqrt_mul (by norm_num) _
  rw [hs, mul_pow, mul_pow, ← pow_mul, mul_add, mul_one, pow_add]
  have h1 : (2:ℝ)^m ≤ (256:ℝ)^d := by
    calc (2:ℝ)^m ≤ (2:ℝ)^d := pow_le_pow_right₀ (by norm_num) hm
      _ ≤ (256:ℝ)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have h2 : (Real.sqrt 2)^(m*n) ≤ (256:ℝ)^(m*n) := by
    apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h3 : (128:ℝ)^(d*n) ≤ (256:ℝ)^(d*n) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h4 : (0:ℝ) ≤ (Real.sqrt d)^(m*n) := by positivity
  calc (2:ℝ)^m * ((Real.sqrt 2)^(m*n) * (Real.sqrt d)^(m*n)) * (128:ℝ)^(d*n)
      = ((2:ℝ)^m * (128:ℝ)^(d*n) * (Real.sqrt 2)^(m*n)) * (Real.sqrt d)^(m*n) := by ring
    _ ≤ ((256:ℝ)^d * (256:ℝ)^(d*n) * (256:ℝ)^(m*n)) * (Real.sqrt d)^(m*n) := by gcongr
    _ = _ := by ring
