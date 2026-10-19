-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.ScalarEntropy.negMulLog_subprob
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:07:28.224019+00:00
-- url     : https://prove2.me/submissions/a565652f-1032-4a18-aae4-cb290a7dce00

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/RelativeEntropy.lean:L13-L30
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.ScalarEntropy.negMulLog_subprob. The node keeps its source
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

-- ---- from OAI.Probability.EntangledGames.RelativeEntropy ----
namespace OAI

universe u_ι u_α u_β u_n u_m

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ThresholdParallelRepetition
namespace ScalarEntropy

lemma negMulLog_subprob {ι : Type u_ι} [Fintype ι]
    (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i ≤ 1)
    (ht : ∀ i, 0 ≤ t i) :
    (∑ i, w i * Real.negMulLog (t i)) ≤ Real.negMulLog (∑ i, w i*t i) := by
  let W : Option ι → ℝ := fun i => i.elim (1-∑ j, w j) w
  let T : Option ι → ℝ := fun i => i.elim 0 t
  have hW : ∀ i, 0 ≤ W i := by
    intro i; cases i with
    | none => exact sub_nonneg.mpr hs
    | some i => exact hw i
  have hsum : ∑ i, W i = 1 := by simp [W, Fintype.sum_option]
  have hT : ∀ i, T i ∈ Set.Ici (0 : ℝ) := by
    intro i; cases i with
    | none => change (0 : ℝ) ≤ 0; rfl
    | some i => exact ht i
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := W) (p := T) (fun i _ => hW i) hsum (fun i _ => hT i)
  simpa [W, T, Fintype.sum_option] using h

open FiniteProbability
variable {α : Type u_α} {β : Type u_β} [Fintype α] [Fintype β]

end ScalarEntropy
namespace OperatorEntropy
open Resolvent QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

variable {m : Type u_m} [Fintype m] [DecidableEq m]

end OperatorEntropy
end ThresholdParallelRepetition

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.ScalarEntropy
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution.{u_ι} : type_of% @_root_.OAI.ThresholdParallelRepetition.ScalarEntropy.negMulLog_subprob.{u_ι} := @_root_.OAI.ThresholdParallelRepetition.ScalarEntropy.negMulLog_subprob.{u_ι}
