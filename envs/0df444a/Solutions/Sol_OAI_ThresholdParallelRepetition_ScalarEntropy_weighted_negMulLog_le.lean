-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.ScalarEntropy.weighted_negMulLog_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:08:59.626175+00:00
-- url     : https://prove2.me/submissions/594bb40f-4e43-48e3-9190-80e7fd26f971

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/RelativeEntropy.lean:L47-L68
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.ScalarEntropy.weighted_negMulLog_le. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_ScalarEntropy_negMulLog_subprob

-- ---- from OAI.Probability.EntangledGames.RelativeEntropy ----
namespace OAI

universe u_ι u_α u_β u_n u_m

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ThresholdParallelRepetition
namespace ScalarEntropy

lemma weighted_negMulLog_le {ι : Type u_ι} [Fintype ι]
    (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 ≤ t i)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ i, w i ≤ d) (hp : 0 < p)
    (hm : ∑ i, w i*t i = p) :
    (∑ i, w i*Real.negMulLog (t i)) ≤ p*Real.log (d/p) := by
  have hw' : ∀ i, 0 ≤ w i/d := fun i => div_nonneg (hw i) hd.le
  have hs' : ∑ i, w i/d ≤ 1 := by rw [← Finset.sum_div]; exact (div_le_one hd).mpr hs
  have h := negMulLog_subprob (fun i => w i/d) t hw' hs' ht
  have hm' : (∑ i, w i/d*t i) = p/d := by
    simp_rw [div_mul_eq_mul_div]; rw [← Finset.sum_div, hm]
  rw [hm'] at h
  have hleft : (∑ i, w i/d*Real.negMulLog (t i)) =
      (∑ i, w i*Real.negMulLog (t i))/d := by
    simp_rw [div_mul_eq_mul_div]; rw [Finset.sum_div]
  rw [hleft] at h
  have h := (div_le_iff₀ hd).mp h
  have he : Real.negMulLog (p/d)*d = p*Real.log (d/p) := by
    change -(p/d)*Real.log (p/d)*d = p*Real.log (d/p)
    rw [Real.log_div hp.ne' hd.ne', Real.log_div hd.ne' hp.ne']
    field_simp
    ring
  exact h.trans_eq he

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


theorem solution.{u_ι} : type_of% @_root_.OAI.ThresholdParallelRepetition.ScalarEntropy.weighted_negMulLog_le.{u_ι} := @_root_.OAI.ThresholdParallelRepetition.ScalarEntropy.weighted_negMulLog_le.{u_ι}
