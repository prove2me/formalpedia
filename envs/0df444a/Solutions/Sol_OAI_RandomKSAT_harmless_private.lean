-- Prove2me | solution 1 for OAI.RandomKSAT.harmless_private
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:48:48.990172+00:00
-- url     : https://prove2.me/submissions/d32bac06-7ab1-45d8-be5e-60aece7d0b48

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BystanderStops.lean:L63-L80
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.harmless_private. The node keeps its source
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

lemma harmless_private {n k : ℕ} (c : Clause n k) (l : List (Clause n k))
    (v : c.1.1) (hv : ∀ d ∈ l, v.val ∉ d.1.1) : Harmless c l := by
  intro r hr
  constructor
  · exact listSAT_sublist (List.sublist_cons_self _ _)
  · rintro ⟨a,ha⟩
    refine ⟨Function.update a v.val (c.2 v), ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with he | hd
    · subst d
      exact ⟨v,by simp⟩
    · obtain ⟨w,hw⟩ := ha d hd
      refine ⟨w,?_⟩
      have hne : w.val ≠ v.val := by
        intro he
        apply hv d (hr.subset hd)
        exact he ▸ w.property
      simpa only [Function.update_of_ne hne] using hw

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.harmless_private := @_root_.OAI.RandomKSAT.harmless_private
