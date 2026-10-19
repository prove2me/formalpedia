-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.FiniteProbability.Law.kl_tilt_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:06:08.01965+00:00
-- url     : https://prove2.me/submissions/1dce4a22-ee7e-4cae-a1e8-572f597fbcc3

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/FiniteProbability.lean:L334-L347
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.FiniteProbability.Law.kl_tilt_le. The node keeps its source
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

section Pair
variable [DecidableEq α] [DecidableEq β]

end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

end Pi

section Information

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
omit [DecidableEq α] in
lemma kl_tilt (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) :
    (p.tilt f hf ht).kl p = p.avg (fun x => f x*Real.log (f x)) := by
  simp only [kl, avg, tilt, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p.weight x = 0
  · simp [h]
  · rw [mul_div_cancel_left₀ _ h, mul_assoc]

omit [DecidableEq α] in
lemma kl_tilt_le (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1)
    {B : ℝ} (_hB : 0 < B) (hb : ∀ x, f x ≤ B) : (p.tilt f hf ht).kl p ≤ Real.log B := by
  rw [kl_tilt]
  have h := p.avg_mono (fun x => show f x*Real.log (f x) ≤ f x*Real.log B from by
    by_cases hz : f x = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log
        (lt_of_le_of_ne (hf x) (Ne.symm hz)) (hb x)) (hf x))
  have he : p.avg (fun x => f x*Real.log B) = Real.log B := by
    simp only [avg, smul_eq_mul, ← mul_assoc, ← Finset.sum_mul]
    change p.avg f*Real.log B = _
    rw [ht, one_mul]
  exact h.trans_eq he

end Information

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.FiniteProbability OAI.ThresholdParallelRepetition.FiniteProbability.Law
open scoped BigOperators


theorem solution.{u_α} : type_of% @_root_.OAI.ThresholdParallelRepetition.FiniteProbability.Law.kl_tilt_le.{u_α} := @_root_.OAI.ThresholdParallelRepetition.FiniteProbability.Law.kl_tilt_le.{u_α}
