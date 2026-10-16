-- Prove2me | solution 1 for OAI.RandomKSAT.lt_listStop_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:47:28.364211+00:00
-- url     : https://prove2.me/submissions/7dee56fc-40f7-4ccf-af5d-e1559ff9f895

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BystanderStops.lean:L40-L54
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.lt_listStop_iff. The node keeps its source
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

-- ---- from OAI.Probability.SATVariance.BystanderStops ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma listSAT_sublist {n k : ℕ} {l r : List (Clause n k)} (h : l.Sublist r)
    (hr : listSAT r) : listSAT l := by
  obtain ⟨a,ha⟩ := hr
  exact ⟨a,fun c hc => ha c (h.subset hc)⟩

lemma listStop_le {n k : ℕ} (l : List (Clause n k)) : listStop l ≤ l.length+1 :=
  Nat.find_min' _ (Or.inl rfl)

lemma lt_listStop_iff {n k m : ℕ} (l : List (Clause n k)) :
    m < listStop l ↔ m ≤ l.length ∧ listSAT (l.take m) := by
  constructor
  · intro hm
    refine ⟨by have := listStop_le l; omega, ?_⟩
    have hh := Nat.find_min (show ∃ j : ℕ, j = l.length+1 ∨ ¬listSAT (l.take j)
      from ⟨_,Or.inl rfl⟩) hm
    exact not_not.mp (fun h => hh (Or.inr h))
  · rintro ⟨hm,hs⟩
    apply (Nat.lt_find_iff _ _).mpr
    intro j hj
    rintro (he | hn)
    · omega
    · apply hn
      exact listSAT_sublist (List.take_sublist_take_left hj) hs

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.lt_listStop_iff := @_root_.OAI.RandomKSAT.lt_listStop_iff
