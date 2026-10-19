-- Prove2me | solution 1 for OAI.Barnette.SimpleCycle.delete_vertex_connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:01:22.009457+00:00
-- url     : https://prove2.me/submissions/bf963287-8bdd-4833-bc84-7fe1e362f525

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CappedDuality.lean:L223-L247
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.SimpleCycle.delete_vertex_connected. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Theorems.Thm_OAI_Barnette_SimpleCycle_cycle_at_of_connected_two

-- ---- from OAI.Combinatorics.Hamiltonian.CappedDuality ----
namespace OAI

/-! Exact duals of capped graphs and Hamiltonian walks in degree-two graphs. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
universe uF
variable {V E W K : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  [Fintype W] [Fintype K]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
universe uF
variable {V E : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.SimpleCycle
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
lemma induced_support_connected {a b : V} (p : G.Walk a b) (s : Set V)
    (hs : ∀ v, v ∈ s ↔ v ∈ p.support) : (G.induce s).Connected := by
  have hw : ∀ v ∈ p.support, v ∈ s := fun v hv => (hs v).mpr hv
  let q := p.induce s hw
  have hq (v : s) : v ∈ q.support := by
    simp only [q, SimpleGraph.Walk.support_induce, List.mem_attachWith]
    exact (hs v).mp v.property
  let : Nonempty s := ⟨⟨a,hw a p.start_mem_support⟩⟩
  exact ⟨fun x y => ((q.takeUntil x (hq x)).reverse.append (q.takeUntil y (hq y))).reachable⟩

lemma delete_vertex_connected (hc : G.Connected) (hd : G.IsRegularOfDegree 2) (v : V) :
    (G.induce {w | w ≠ v}).Connected := by
  obtain ⟨p,hp⟩ := cycle_at_of_connected_two G hc hd v
  have hn : ¬p.tail.Nil := by
    intro hh
    have hl := hp.isCycle.three_le_length
    have ht := SimpleGraph.Walk.length_eq_zero_iff.mpr hh
    simp only [SimpleGraph.Walk.length_tail] at ht
    omega
  have heq := p.tail.support_dropLast_concat hn
  have hnmem : v ∉ p.tail.dropLast.support := by
    have hnd := hp.isHamiltonian_tail.isPath.support_nodup
    rw [← heq] at hnd
    intro hm
    exact (List.nodup_append.mp hnd).2.2 v hm v (by simp) rfl
  apply induced_support_connected G p.tail.dropLast
  intro w
  constructor
  · intro hw
    have hm := hp.isHamiltonian_tail.mem_support w
    rw [←heq, List.mem_append, List.mem_singleton] at hm
    exact hm.resolve_right hw
  · intro hw h
    subst w
    exact hnmem hw
end
end Barnette.SimpleCycle

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.SimpleCycle
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.SimpleCycle.delete_vertex_connected := @_root_.OAI.Barnette.SimpleCycle.delete_vertex_connected
