-- Prove2me | solution 1 for OAI.RandomKSAT.min_isolate_mean_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:00:57.548921+00:00
-- url     : https://prove2.me/submissions/abdb6d26-3930-4872-9404-86b368fb4151

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BystanderVariance.lean:L214-L229
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.min_isolate_mean_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance
import Definitions.Def_OAI_Probability_SATVariance_IsolatedSupports
import Definitions.Def_OAI_Probability_SATVariance_BystanderVariance

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_mono.{u_1} {α : Type u_1} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    favg f ≤ favg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BystanderVariance ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma min_isolate_mean_lower {n k M Q : ℕ} (hM : 0 < M) (hQ : Q ≤ M)
    {β : ℝ} (hmean : (M:ℝ)*β ≤ favg (fun w : Fin M → Clause n k => ((isolateSet w).card:ℝ))) :
    (Q:ℝ)*β ≤ favg (fun w : Fin M → Clause n k => (min Q (isolateSet w).card:ℝ)) := by
  have hh (w : Fin M → Clause n k) :
      (Q:ℝ)*(isolateSet w).card ≤ (M:ℝ)*(min Q (isolateSet w).card:ℝ) := by
    have hJ : (isolateSet w).card ≤ M := by simpa using Finset.card_le_univ (isolateSet w)
    have ht : Q*(isolateSet w).card ≤ M*min Q (isolateSet w).card := by
      by_cases h : Q ≤ (isolateSet w).card
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right (by omega)]; nlinarith
    exact_mod_cast ht
  have ht := favg_mono hh
  rw [favg_mul,favg_mul] at ht
  have hh' := mul_le_mul_of_nonneg_left hmean (show (0:ℝ) ≤ Q by positivity)
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  nlinarith

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.min_isolate_mean_lower := @_root_.OAI.RandomKSAT.min_isolate_mean_lower
