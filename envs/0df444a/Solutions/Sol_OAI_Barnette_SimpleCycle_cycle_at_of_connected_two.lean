-- Prove2me | solution 1 for OAI.Barnette.SimpleCycle.cycle_at_of_connected_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:59:57.702143+00:00
-- url     : https://prove2.me/submissions/0c9d30ad-26a9-4321-b915-e8605076edea

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CappedDuality.lean:L187-L210
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.SimpleCycle.cycle_at_of_connected_two. The node keeps its source
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

lemma cycle_at_of_connected_two [DecidableEq V] (hc : G.Connected) (hd : G.IsRegularOfDegree 2) (v : V) :
    ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  have hi : G.IsCycles := by
    intro w _
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    exact hd w
  have hn : (G.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    have hh : (G.neighborSet v).ncard = 2 := by
      rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
      exact hd v
    omega
  obtain ⟨p,hp,hs⟩ := hi.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := G.connectedComponentMk v) rfl hn
  refine ⟨p,hp,hp.isPath_tail.isHamiltonian_of_mem ?_⟩
  intro w
  by_cases hw : w = v
  · subst w
    exact p.tail.end_mem_support
  · have hm : w ∈ p.support := by
      rw [← p.mem_verts_toSubgraph, hs]
      exact SimpleGraph.ConnectedComponent.eq.mpr (hc w v)
    rw [← p.cons_support_tail hp.not_nil] at hm
    exact (List.mem_cons.mp hm).resolve_left hw

end
end Barnette.SimpleCycle

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.SimpleCycle
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.SimpleCycle.cycle_at_of_connected_two := @_root_.OAI.Barnette.SimpleCycle.cycle_at_of_connected_two
