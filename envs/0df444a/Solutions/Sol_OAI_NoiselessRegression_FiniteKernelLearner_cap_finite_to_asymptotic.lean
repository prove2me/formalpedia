-- Prove2me | solution 1 for OAI.NoiselessRegression.FiniteKernelLearner.cap_finite_to_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:39:56.372115+00:00
-- url     : https://prove2.me/submissions/c042e04c-fda9-46e3-86bf-1e4462aea14e

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

open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u


theorem solution (C : ℝ) {d M : ℕ} (hd : 32 ≤ d)
    (hM : (M:ℝ) ≤ (d:ℝ)^2) (ε α : ℝ) (n : ℕ) (hε : 0 ≤ ε) :
    Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)))^n ≤
      Real.exp ((C+32)*d*(1+n))*(ε/2)^α := by
  have hd' : (32:ℝ) ≤ d := by exact_mod_cast hd
  have hkN : d ≤ 32 * (d/16) := by omega
  have hk : (d:ℝ)/32 ≤ ((d/16:ℕ):ℝ) := by
    have : (d:ℝ) ≤ 32 * ((d/16:ℕ):ℝ) := by exact_mod_cast hkN
    linarith
  have hkpos : (0:ℝ) < ((d/16:ℕ):ℝ) := by linarith
  have hMk : (M:ℝ)/((d/16:ℕ):ℝ) ≤ 32*d := by
    rw [div_le_iff₀ hkpos]
    nlinarith
  have hM0 : 0 ≤ (M:ℝ)/((d/16:ℕ):ℝ) := by positivity
  have h2 : (2:ℝ)^((M:ℝ)/(d/16:ℕ)) ≤ Real.exp (32*d) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have := Real.log_two_lt_d9
    nlinarith
  have hA : 0 ≤ (ε/2)^α := Real.rpow_nonneg (by linarith) _
  have hB : Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)) ≤ Real.exp (C*d + 32*d) := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hB0 : 0 ≤ Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)) := by positivity
  have hpow := pow_le_pow_left₀ hB0 hB n
  rw [← Real.exp_nat_mul] at hpow
  calc Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)))^n
      ≤ Real.exp (C*d)*(ε/2)^α*Real.exp (n*(C*d+32*d)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Real.exp (C*d + n*(C*d+32*d) + 0)*(ε/2)^α := by
        rw [add_zero, Real.exp_add]; ring
    _ ≤ Real.exp ((C+32)*d*(1+n))*(ε/2)^α := by
        apply mul_le_mul_of_nonneg_right _ hA
        apply Real.exp_le_exp.mpr
        nlinarith

