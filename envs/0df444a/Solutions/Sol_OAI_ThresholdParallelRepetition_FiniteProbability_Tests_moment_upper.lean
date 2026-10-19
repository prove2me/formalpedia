-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.FiniteProbability.Tests.moment_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:46:08.212796+00:00
-- url     : https://prove2.me/submissions/085f5547-3974-4a91-a136-1270a640e720

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/TestMoments.lean:L64-L86
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.FiniteProbability.Tests.moment_upper. The node keeps its source
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

lemma avg_add (p : Law α) (f g : α → E) :
    p.avg (fun x => f x+g x) = p.avg f+p.avg g := by
  simp [avg, smul_add, Finset.sum_add_distrib]
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
omit [Nonempty I] [Fintype Ω] in
lemma event_insert (c : Finset I) (i : I) (ω : Ω) :
    event win (insert i c) ω = event win c ω*(if win ω i then 1 else 0) := by
  simp only [event, Finset.forall_mem_insert]
  split_ifs <;> simp_all
omit [Fintype Ω] in
lemma avg_event_insert (c : Finset I) (ω : Ω) :
    (uniform (R := I)).avg (fun i => event win (insert i c) ω) = event win c ω*rate win ω := by
  simp only [event_insert]
  change (uniform (R := I)).avg (fun i => event win c ω • (if win ω i then (1:ℝ) else 0)) = _
  rw [avg_smul]; rfl
lemma moment_zero (c : Finset I) : moment ρ win c 0 = mass ρ win c := by simp only [moment, pow_zero, mul_one, mass]
lemma moment_step (c : Finset I) (t : ℕ) :
    moment ρ win c (t+1) = (uniform (R := I)).avg (fun i => moment ρ win (insert i c) t) := by
  unfold moment
  rw [avg_comm]
  apply congrArg ρ.avg
  funext ω
  have he : (fun i => event win (insert i c) ω * rate win ω^t) =
      (fun i => (rate win ω^t) • event win (insert i c) ω) := by funext i; simp only [smul_eq_mul, mul_comm]
  rw [he, avg_smul, avg_event_insert, pow_succ]
  change _ = _*_
  ring

lemma moment_upper {r e : ℝ} (hr : 0 ≤ r) (_he : 0 ≤ e) (T : ℕ)
    (hstep : ∀ c : Finset I, c.card < T →
      (uniform (R := I)).avg (fun i => mass ρ win (insert i c)) ≤ r*mass ρ win c+e) :
    ∀ t : ℕ, ∀ c : Finset I, c.card+t ≤ T →
      moment ρ win c t ≤ r^t*mass ρ win c + e*∑ s ∈ Finset.range t, r^s := by
  intro t
  induction t with
  | zero => intro c hc; simp only [moment_zero, pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]; exact le_rfl
  | succ t ih =>
    intro c hc
    rw [moment_step]
    have hbound := (uniform (R := I)).avg_mono (fun i => ih (insert i c) (by
      have hi := Finset.card_insert_le i c
      omega))
    have heq : (uniform (R := I)).avg (fun i => r^t*mass ρ win (insert i c)+e*∑ s ∈ Finset.range t, r^s) =
        r^t*(uniform (R := I)).avg (fun i => mass ρ win (insert i c))+e*∑ s ∈ Finset.range t, r^s := by
      rw [avg_add, avg_const]
      change (uniform (R := I)).avg (fun i => (r^t) • mass ρ win (insert i c)) + _ = _
      rw [avg_smul]; rfl
    rw [heq] at hbound
    have hs := mul_le_mul_of_nonneg_left (hstep c (by omega)) (pow_nonneg hr t)
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

end Tests
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.FiniteProbability OAI.ThresholdParallelRepetition.FiniteProbability.Tests
open scoped BigOperators
open Law


theorem solution.{u_I,u_Ω} : type_of% @_root_.OAI.ThresholdParallelRepetition.FiniteProbability.Tests.moment_upper.{u_I,u_Ω} := @_root_.OAI.ThresholdParallelRepetition.FiniteProbability.Tests.moment_upper.{u_I,u_Ω}
