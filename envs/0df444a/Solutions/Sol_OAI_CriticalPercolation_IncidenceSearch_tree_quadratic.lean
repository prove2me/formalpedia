-- Prove2me | solution 1 for OAI.CriticalPercolation.IncidenceSearch.tree_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:55.183203+00:00
-- url     : https://prove2.me/submissions/c2c53251-1b6e-4b6f-bd6e-be4dac68b287

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_IncidenceSearch_compile_terminal

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ComponentSelf
attribute [-simp] _root_.OAI.CriticalPercolation.ClusterDeletion.component_bot _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
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

namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}

lemma roots_singleton (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]

end CriticalPercolation.ClusterDeletion

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

lemma terminal_cluster (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (ht : ¬∃ e, Available G v st e) :
    G.cluster ω v = G.cluster (st.opened : Set E) v ∧
      (st.read : Set E) = G.incidentEdges (G.cluster ω v) := by
  have hread : ∀ e ∈ G.incidentEdges (G.cluster (st.opened : Set E) v), e ∈ st.read := by
    intro e he
    by_contra hh
    exact ht ⟨e,hh,he⟩
  have hc : G.cluster ω v = G.cluster (st.opened : Set E) v := by
    have hh := G.roots_eq_of_incident (S := {v}) (U := G.cluster (st.opened : Set E) v)
      (ω := (st.opened : Set E)) (ω' := ω)
      (by simp only [ClusterDeletion.roots_singleton,ClusterDeletion.component,BondGraph.cluster])
      (fun e he => hs.2.1 e (hread e he))
    simpa only [ClusterDeletion.roots_singleton,ClusterDeletion.component,BondGraph.cluster] using hh
  refine ⟨hc,?_⟩
  rw [hc]
  exact Set.Subset.antisymm hs.2.2 hread

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceIdentity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
variable {V E : Type*}

variable [Fintype E]

lemma tree_read (G : BondGraph V E) (v : V) (ω : Set E) :
    (((tree G v).run (fun e => decide (e∈ω))).read : Set E) =
      G.incidentEdges (G.cluster ω v) := by
  have hg : Good G v ω (⟨∅,∅⟩ : State E) := by simp [Good]
  have hh := compile_terminal G v ω (Fintype.card E+1) ⟨∅,∅⟩ hg (by simp)
  exact (terminal_cluster G v ω _ hh.1 hh.2).2

lemma tree_mem_read (G : BondGraph V E) (v : V) (ω : Set E) (e : E) :
    e ∈ ((tree G v).run (fun a => decide (a∈ω))).read ↔
      e ∈ G.incidentEdges (G.cluster ω v) := by
  exact Set.ext_iff.mp (tree_read G v ω) e

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedIncidenceSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

lemma compile_weighted_trace (G : BondGraph V E) (v : V) (n : ℕ) (st : State E)
    (ω : Set E) (a : E → ℝ) (p : ℝ) :
    let t := compile G v n st
    let out := t.run (fun e => decide (e∈ω))
    t.weightedSum a p ω + weightedRead a p ω st = weightedRead a p ω out ∧
    t.quadraticCost a ω + quadraticRead a st = quadraticRead a out := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.weightedSum,SearchTree.quadraticCost]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : e∉st.read := h.choose_spec.1
      have hopen := ih (st.open e)
      have hclosed := ih (st.closed e)
      have hs : weightedRead a p ω (st.open e) =
          (if e∈ω then a e*(1-p) else -a e*p)+weightedRead a p ω st := by
        simp only [weightedRead,State.open,Finset.sum_insert he]
      have hs' : weightedRead a p ω (st.closed e) =
          (if e∈ω then a e*(1-p) else -a e*p)+weightedRead a p ω st := by
        simp only [weightedRead,State.closed,Finset.sum_insert he]
      have hq : quadraticRead a (st.open e) = (a e)^2+quadraticRead a st := by
        simp only [quadraticRead,State.open,Finset.sum_insert he]
      have hq' : quadraticRead a (st.closed e) = (a e)^2+quadraticRead a st := by
        simp only [quadraticRead,State.closed,Finset.sum_insert he]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        (if ω e then a e*(1-p)+(compile G v n (st.open e)).weightedSum a p ω else
          -a e*p+(compile G v n (st.closed e)).weightedSum a p ω) + weightedRead a p ω st =
          weightedRead a p ω out ∧
        ((a e)^2 + if ω e then (compile G v n (st.open e)).quadraticCost a ω else
          (compile G v n (st.closed e)).quadraticCost a ω) + quadraticRead a st = quadraticRead a out)
      by_cases hω : e∈ω
      · have hω' : ω e := hω
        simp only [hω,hω',decide_true,ite_true, if_true]
        dsimp only at hopen
        rw [hs,hq,ite_eq_left hω] at hopen
        constructor <;> linarith [hopen.1,hopen.2]
      · have hω' : ¬ω e := hω
        simp only [hω,hω',decide_false,Bool.false_eq_true,ite_false, if_false]
        dsimp only at hclosed
        rw [hs',hq',ite_eq_right hω] at hclosed
        constructor <;> linarith [hclosed.1,hclosed.2]
    · simp [SearchTree.run,SearchTree.weightedSum,SearchTree.quadraticCost]

variable [Fintype E]

lemma tree_quadratic_oai (G : BondGraph V E) (v : V) (ω : Set E) (a : E → ℝ) :
    (tree G v).quadraticCost a ω = ∑ e,
      if e∈G.incidentEdges (G.cluster ω v) then (a e)^2 else 0 := by
  have h := (compile_weighted_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω a 0).2
  change (tree G v).quadraticCost a ω + quadraticRead a ⟨∅,∅⟩ =
    quadraticRead a ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [quadraticRead,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then (a e)^2 else 0 := by
      simp only [←Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [tree_mem_read]

end CriticalPercolation.IncidenceSearch
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.IncidenceSearch.tree_quadratic_oai.{u_1, u_2} := @OAI.CriticalPercolation.IncidenceSearch.tree_quadratic_oai.{u_1, u_2}
