-- Prove2me | solution 2 for OAI.ThresholdParallelRepetition.FiniteProbability.Tests.threshold_moment_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:47:38.524018+00:00
-- url     : https://prove2.me/submissions/121dea2d-e8ba-4fad-956a-259a82ebe5df

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/TestMoments.lean:L88-L102
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.FiniteProbability.Tests.threshold_moment_lower. The node keeps its source
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

-- ---- from OAI.Probability.EntangledGames.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_β u_γ u_E u_F u_ι

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability

namespace Law
variable {α : Type u_α} {β : Type u_β} {γ : Type u_γ} {E : Type u_E} [Fintype α] [Fintype β] [Fintype γ]
  [AddCommMonoid E] [Module ℝ E]

lemma avg_smul (p : Law α) (r : ℝ) (f : α → E) :
    p.avg (fun x => r • f x) = r • p.avg f := by
  simp only [avg, Finset.smul_sum, smul_comm (p.weight _) r]
section Pair
variable [DecidableEq α] [DecidableEq β]

end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

end Pi

section Information

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
end Information

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- from OAI.Probability.EntangledGames.TestMoments ----
namespace OAI

universe u_I u_Ω

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Tests
open Law
variable {I : Type u_I} {Ω : Type u_Ω} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]
  (ρ : Law Ω) (win : Ω → I → Bool)
omit [DecidableEq I] [Fintype Ω] in
lemma rate_nonneg (ω : Ω) : 0 ≤ rate win ω := by
  apply avg_nonneg; intro i; split_ifs <;> norm_num
omit [Nonempty I] [Fintype Ω] in
lemma event_empty (ω : Ω) : event win ∅ ω = 1 := by simp [event]
lemma threshold_moment_lower {q : ℝ} (hq : 0 ≤ q) (t : ℕ) :
    (ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0))*q^t ≤ moment ρ win ∅ t := by
  have he : (ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0))*q^t =
      ρ.avg (fun ω => if q ≤ rate win ω then q^t else 0) := by
    rw [mul_comm]
    change (q^t) • ρ.avg (fun ω => if q ≤ rate win ω then (1:ℝ) else 0) = _
    rw [← avg_smul]
    congr 1; funext ω; split_ifs <;> simp
  rw [he]
  apply ρ.avg_mono
  intro ω
  simp only [event_empty, one_mul]
  split_ifs with h
  · exact pow_le_pow_left₀ hq h _
  · exact pow_nonneg (rate_nonneg win ω) _
end Tests
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.FiniteProbability OAI.ThresholdParallelRepetition.FiniteProbability.Tests
open scoped BigOperators
open Law


theorem solution.{u_I,u_Ω} : type_of% @_root_.OAI.ThresholdParallelRepetition.FiniteProbability.Tests.threshold_moment_lower.{u_I,u_Ω} := @_root_.OAI.ThresholdParallelRepetition.FiniteProbability.Tests.threshold_moment_lower.{u_I,u_Ω}
