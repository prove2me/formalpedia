-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.RepeatedModel.unconditional_rate_le_value
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:53:18.934122+00:00
-- url     : https://prove2.me/submissions/836d081e-9230-4111-867e-3927994520f2

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ConditionedStep.lean:L83-L95
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.RepeatedModel.unconditional_rate_le_value. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_RepeatedModel_good_event_step

-- ---- from OAI.Probability.EntangledGames.RepeatedModel ----
namespace OAI

universe u_X u_Y u_A u_B u_I u_m u_n

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (M : RepeatedModel X Y A B I m n)
lemma mass_empty : M.mass ∅ = 1 := by
  have he : M.indicator ∅ = fun _ => (1:ℝ) := by funext t; simp [indicator]
  rw [mass, he, avg_const]
end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace FiniteProbability.Law
variable {I : Type u_I} {X : Type u_X} {Y : Type u_Y} [DecidableEq I]
end FiniteProbability.Law
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI

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

omit hμ hV [Nonempty m] [Nonempty n] in
lemma mean_eq_first_test : M.joint.avg (Tests.rate M.winsAt) =
    (uniform (R := I)).avg (fun i => M.mass (insert i ∅)) := by
  unfold Tests.rate
  rw [avg_comm]
  congr 1
  funext i
  unfold mass
  congr 1
  funext ω
  simp [indicator]

lemma unconditional_rate_le_value : M.joint.avg (Tests.rate M.winsAt) ≤ entangledValue G := by
  rw [M.mean_eq_first_test]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < min ε 1 := lt_min hε zero_lt_one
  have hδ1 : min ε 1 ≤ 1 := min_le_right _ _
  have hh := M.good_event_step G hμ hV ∅ (by rw [M.mass_empty]; norm_num)
    (by simpa using Fintype.card_pos (α := I)) hδ hδ1 (by simp; positivity) (by
      simp only [Finset.card_empty, pow_zero, M.mass_empty, div_one, Real.log_one, zero_div]
      positivity)
  rw [M.mass_empty, mul_one] at hh
  have hε' := min_le_left ε 1
  linarith

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
namespace ThresholdParallelRepetition

end ThresholdParallelRepetition

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.RepeatedModel
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling FiniteProbability Law MixedExposure


theorem solution : type_of% @_root_.OAI.ThresholdParallelRepetition.RepeatedModel.unconditional_rate_le_value := @_root_.OAI.ThresholdParallelRepetition.RepeatedModel.unconditional_rate_le_value
