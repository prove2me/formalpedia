-- Prove2me | solution 1 for OAI.RandomKSAT.selected_perm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:56:24.068994+00:00
-- url     : https://prove2.me/submissions/62fc1acb-69a2-40a7-842f-89245ad7c545

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/BystanderVariance.lean:L152-L170
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.selected_perm. The node keeps its source
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

-- ---- from OAI.Probability.SATVariance.BystanderVariance ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma selected_perm {n k M : ℕ} (Q : ℕ) (w : Fin M → Clause n k) :
    ((bystanderList Q w)++(activeList Q w)).Perm (List.ofFn w) := by
  let I := chosenIsolates Q w
  have hnd : (I.toList++(Finset.univ\I).toList).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro i hi j hj he
    subst j
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hj)).2 (Finset.mem_toList.mp hi)
  have hid : (List.ofFn (id : Fin M → Fin M)).Nodup := List.nodup_ofFn.mpr Function.injective_id
  have hp : (I.toList++(Finset.univ\I).toList).Perm (List.ofFn (id : Fin M → Fin M)) := by
    rw [List.perm_ext_iff_of_nodup hnd hid]
    intro i
    simp only [List.mem_append,Finset.mem_toList,Finset.mem_sdiff,Finset.mem_univ,true_and,List.mem_ofFn]
    simp only [id_eq,exists_eq,iff_true]
    exact em (i ∈ I)
  have hh := hp.map w
  change ((I.toList.map w)++((Finset.univ\I).toList.map w)).Perm (List.ofFn w)
  simpa only [List.map_append,List.map_ofFn,Function.comp_id] using hh

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.selected_perm := @_root_.OAI.RandomKSAT.selected_perm
