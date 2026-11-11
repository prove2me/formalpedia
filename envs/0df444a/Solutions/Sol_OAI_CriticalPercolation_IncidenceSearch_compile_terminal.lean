-- Prove2me | solution 1 for OAI.CriticalPercolation.IncidenceSearch.compile_terminal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:22.699693+00:00
-- url     : https://prove2.me/submissions/0b232ab9-7767-4266-b4bb-af81805b889b

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterObject
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

lemma incidentEdges_mono {S T : Set V} (h : S ⊆ T) : G.incidentEdges S ⊆ G.incidentEdges T := by
  rintro e ⟨v, hv, he⟩
  exact ⟨v, h hv, he⟩

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch

variable {V E : Type*} [DecidableEq E]

lemma good_closed (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∉ ω) :
    Good G v ω (st.closed e) := by
  refine ⟨fun a ha => Finset.mem_insert_of_mem (hs.1 ha),?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_false (fun h => he.1 (hs.1 h)) hω
    · exact hs.2.1 a ha
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha

lemma good_open (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∈ ω) :
    Good G v ω (st.open e) := by
  refine ⟨Finset.insert_subset_insert e hs.1,?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_true (Finset.mem_insert_self _ _) hω
    · have hae : a≠e := fun hh => he.1 (hh ▸ ha)
      simpa only [State.open,Finset.mem_insert,hae,false_or] using hs.2.1 a ha
  · intro a ha
    change a ∈ G.incidentEdges (G.cluster ((insert e st.opened : Finset E) : Set E) v)
    rw [Finset.coe_insert]
    apply G.incidentEdges_mono (G.cluster_mono (Set.subset_insert e (st.opened : Set E)) v)
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha

variable [Fintype E]

lemma compile_terminal_oai (G : BondGraph V E) (v : V) (ω : Set E) (n : ℕ) (st : State E)
    (hs : Good G v ω st) (hn : Fintype.card E - st.read.card < n) :
    let out := (compile G v n st).run (fun e => decide (e∈ω))
    Good G v ω out ∧ ¬∃ e, Available G v out e := by
  induction n generalizing st with
  | zero => omega
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : Available G v st e := h.choose_spec
      have hc : (insert e st.read).card = st.read.card+1 := Finset.card_insert_of_notMem he.1
      have hle : st.read.card < Fintype.card E := by
        have hh := Finset.card_le_univ (s := insert e st.read)
        rw [hc] at hh
        omega
      have hn' : Fintype.card E - (insert e st.read).card < n := by rw [hc]; omega
      simp only [SearchTree.run]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        Good G v ω out ∧ ¬∃ a, Available G v out a)
      by_cases hω : e∈ω
      · simp only [hω,decide_true,ite_true, if_true]
        exact ih (st.open e) (good_open G v ω st hs e he hω) hn'
      · simp only [hω,decide_false,Bool.false_eq_true,ite_false, if_false]
        exact ih (st.closed e) (good_closed G v ω st hs e he hω) hn'
    · exact ⟨hs,h⟩

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.IncidenceSearch.compile_terminal_oai.{u_1, u_2} := @OAI.CriticalPercolation.IncidenceSearch.compile_terminal_oai.{u_1, u_2}
