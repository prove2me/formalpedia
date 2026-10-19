-- Prove2me | solution 2 for OAI.ThresholdParallelRepetition.testing_parameters_good
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:54:58.482331+00:00
-- url     : https://prove2.me/submissions/461b1c1b-bb53-491a-b3cb-4ec4c645cb14

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ConditionedStep.lean:L105-L137
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.testing_parameters_good. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates
import Definitions.Def_OAI_Probability_EntangledGames_FreshStates
import Definitions.Def_OAI_Probability_EntangledGames_ExposureData
import Definitions.Def_OAI_Probability_EntangledGames_Refinement
import Definitions.Def_OAI_Probability_EntangledGames_ExposureErrors
import Definitions.Def_OAI_Probability_EntangledGames_Rounding
import Definitions.Def_OAI_Probability_EntangledGames_RepeatedModel
import Definitions.Def_OAI_Probability_EntangledGames_TestMoments

-- ---- from OAI.Probability.EntangledGames.ConditionedStep ----
namespace OAI

universe u_I

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure

namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
namespace ThresholdParallelRepetition

lemma testing_parameters_good {δ k d p : ℝ} {c : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < k) (hd : 1 ≤ d)
    (hc : (c : ℝ) ≤ δ^9*k/((2:ℝ)^90*(1+Real.log d)))
    (hp : Real.exp (-(δ^8*k/(2:ℝ)^83)) ≤ p) :
    (c : ℝ) ≤ δ*k/4 ∧ (c : ℝ) < k ∧
      Real.log (d^c/p)/(k-(c : ℝ)) ≤ δ^8/(2:ℝ)^80 := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hlog : 0 ≤ Real.log d := Real.log_nonneg hd
  have hD : 0 < (2:ℝ)^90*(1+Real.log d) := by positivity
  have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg c
  have hc' := (le_div_iff₀ hD).mp hc
  have h9 : δ^9 ≤ δ := by simpa using pow_le_pow_of_le_one hδ.le hδ1 (show 1 ≤ 9 by omega)
  have h98 : δ^9 ≤ δ^8 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h9k := mul_le_mul_of_nonneg_right h9 hk.le
  have h98k := mul_le_mul_of_nonneg_right h98 hk.le
  have hcd : (c : ℝ)*(2:ℝ)^90 ≤ δ^9*k := by
    nlinarith [mul_nonneg hc0 hlog]
  have hsize : (c : ℝ) ≤ δ*k/4 := by nlinarith
  have hhalf : (c : ℝ) ≤ k/2 := by nlinarith
  have hck : (c : ℝ) < k := by linarith
  have hp0 : 0 < p := (Real.exp_pos _).trans_le hp
  have hlp := Real.log_le_log (Real.exp_pos _) hp
  rw [Real.log_exp] at hlp
  have hlc : Real.log (d^c/p) ≤ δ^8*k/(2:ℝ)^82 := by
    rw [Real.log_div (pow_ne_zero _ hd0.ne') hp0.ne', Real.log_pow]
    have hclog : (c : ℝ)*Real.log d ≤ δ^8*k/(2:ℝ)^90 := by
      nlinarith
    nlinarith [mul_nonneg (pow_nonneg hδ.le 8) hk.le]
  refine ⟨hsize, hck, ?_⟩
  apply (div_le_iff₀ (sub_pos.mpr hck)).mpr
  have hz : 0 ≤ δ^8 := pow_nonneg hδ.le 8
  have hh := mul_le_mul_of_nonneg_left hhalf hz
  nlinarith

end ThresholdParallelRepetition

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition


theorem solution : type_of% @_root_.OAI.ThresholdParallelRepetition.testing_parameters_good := @_root_.OAI.ThresholdParallelRepetition.testing_parameters_good
