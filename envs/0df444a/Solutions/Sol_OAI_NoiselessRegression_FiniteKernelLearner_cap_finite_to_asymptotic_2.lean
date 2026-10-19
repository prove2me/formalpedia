-- Prove2me | solution 2 for OAI.NoiselessRegression.FiniteKernelLearner.cap_finite_to_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:41:23.975897+00:00
-- url     : https://prove2.me/submissions/30bafb8a-492a-402a-ad42-aae712f9b541

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Asymptotics.lean:L164-L179
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.FiniteKernelLearner.cap_finite_to_asymptotic. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel
import Definitions.Def_OAI_Probability_ProjectionMoments_Seeded

-- ---- from OAI.Probability.ProjectionMoments.Asymptotics ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace Learner
variable {d M T : ℕ} {Ω : Type*} [MeasurableSpace Ω]

end Learner
namespace FiniteKernelLearner

section
universe u

end

section

universe u
variable {d M T : ℕ} {Ξ : Type u} [MeasurableSpace Ξ]

end

universe u

lemma cap_memory_factor (C : ℝ) {d M : ℕ} (hd : 32 ≤ d)
    (hM : (M:ℝ) ≤ (d:ℝ)^2) :
    Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)) ≤ Real.exp ((C+32)*d) := by
  have hk : 0 < (d/16:ℕ) := by omega
  have hkR : (0:ℝ) < (d/16:ℕ) := by exact_mod_cast hk
  have hdk : d ≤ 32*(d/16) := by omega
  have hdkR : (d:ℝ) ≤ 32*(d/16:ℕ) := by exact_mod_cast hdk
  have hfrac : (M:ℝ)/(d/16:ℕ) ≤ 32*d := by
    rw [div_le_iff₀ hkR]
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  rw [Real.rpow_def_of_pos (by norm_num),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hnon : (0:ℝ) ≤ (M:ℝ)/(d/16:ℕ) := by positivity
  have hl := mul_le_mul_of_nonneg_right hlog hnon
  nlinarith

lemma cap_finite_to_asymptotic (C : ℝ) {d M : ℕ} (hd : 32 ≤ d)
    (hM : (M:ℝ) ≤ (d:ℝ)^2) (ε α : ℝ) (n : ℕ) (hε : 0 ≤ ε) :
    Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)))^n ≤
      Real.exp ((C+32)*d*(1+n))*(ε/2)^α := by
  have hbase := cap_memory_factor C hd hM
  have hfront : Real.exp (C*d) ≤ Real.exp ((C+32)*d) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have ht := mul_le_mul (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg (by positivity : 0 ≤ ε/2) α))
    (pow_le_pow_left₀ (by positivity) hbase n) (by positivity) (by positivity)
  apply ht.trans_eq
  rw [← Real.exp_nat_mul]
  calc
    Real.exp ((C+32)*d)*(ε/2)^α*Real.exp ((n:ℝ)*((C+32)*d)) =
        (Real.exp ((C+32)*d)*Real.exp ((n:ℝ)*((C+32)*d)))*(ε/2)^α := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end FiniteKernelLearner
end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.NoiselessRegression.FiniteKernelLearner.cap_finite_to_asymptotic := @_root_.OAI.NoiselessRegression.FiniteKernelLearner.cap_finite_to_asymptotic
