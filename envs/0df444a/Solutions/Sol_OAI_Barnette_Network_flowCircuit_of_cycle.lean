-- Prove2me | solution 1 for OAI.Barnette.Network.flowCircuit_of_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:26:59.520269+00:00
-- url     : https://prove2.me/submissions/47ba651f-989a-4a09-bbac-c83e3c408186

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/FlowCircuits.lean:L345-L359
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.flowCircuit_of_cycle. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Theorems.Thm_OAI_Barnette_Network_flow_no_leaf

-- ---- from OAI.Combinatorics.Hamiltonian.CutSpaces ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cuts, simplicity, and connectivity of finite oriented networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (N : Network V E)

variable [Fintype V] [Fintype E]
variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
lemma incident_iff_mem_pair (e : E) (v : V) :
    N.Incident e v ↔ v ∈ s(N.tail e, N.head e) := by
  simp only [Incident, Sym2.mem_iff]
  tauto

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.FlowCircuits ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Minimal flow circuits, triangular faces, and simple cycle coordinates. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
lemma flowSupport_eq_empty_iff (x : E → ℝ) : N.flowSupport x = ∅ ↔ x = 0 := by
  simp only [Finset.eq_empty_iff_forall_notMem, mem_flowSupport, not_not,
    funext_iff, Pi.zero_apply]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette

open Fin.NatCast

namespace CycleCoordinates

variable {V : Type*} {G : SimpleGraph V} (C : CycleCoordinates G)

end CycleCoordinates
end Barnette

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] [Fintype E] in
lemma cycleEdge_ends (i : Fin (C.n+3)) :
    s(N.tail (N.cycleEdge C i),N.head (N.cycleEdge C i)) = s(C.vertex i,C.vertex (i+1)) :=
  Sym2.eq_iff.mpr (C.adjacent i).2.choose_spec

omit [Fintype V] [Fintype E] in
lemma cycleEdge_incident (i : Fin (C.n+3)) (v : V) :
    N.Incident (N.cycleEdge C i) v ↔ v = C.vertex i ∨ v = C.vertex (i+1) := by
  rw [N.incident_iff_mem_pair, N.cycleEdge_ends]
  exact Sym2.mem_iff

omit [Fintype V] in

lemma cycle_support_minimal (hN : N.Simple) (y : E → ℝ) (hy : N.boundary y = 0)
    (hsub : N.flowSupport y ⊆ N.cycleEdges C) (hne : y ≠ 0) :
    N.flowSupport y = N.cycleEdges C := by
  have hs : (N.flowSupport y).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    exact fun h => hne ((N.flowSupport_eq_empty_iff y).mp h))
  obtain ⟨e,he⟩ := hs
  obtain ⟨q,hq⟩ := (N.mem_cycleEdges C e).mp (hsub he)
  have hq' : y (N.cycleEdge C q) ≠ 0 := by rw [hq]; exact (N.mem_flowSupport _ _).mp he
  have hall : ∀ i, y (N.cycleEdge C i) ≠ 0 := by
    apply Barnette.cyclic_propagation (fun i => y (N.cycleEdge C i) ≠ 0) _ hq'
    intro i hi
    have hv : N.Incident (N.cycleEdge C (i+1)) (C.vertex (i+1)) :=
      (N.cycleEdge_incident C _ _).mpr (Or.inl rfl)
    obtain ⟨f,hfe,hyf,hfv⟩ := N.flow_no_leaf hN y hy hi hv
    obtain ⟨j,rfl⟩ := (N.mem_cycleEdges C f).mp (hsub ((N.mem_flowSupport y f).mpr hyf))
    rcases (N.cycleEdge_incident C j _).mp hfv with hj | hj
    · have hj' := C.vertex.injective hj
      exact (hfe (congrArg (N.cycleEdge C) hj'.symm)).elim
    · have hj' := add_right_cancel (C.vertex.injective hj)
      simpa only [← hj'] using hyf
  apply Finset.Subset.antisymm hsub
  intro e he
  obtain ⟨i,rfl⟩ := (N.mem_cycleEdges C e).mp he
  exact (N.mem_flowSupport y _).mpr (hall i)

omit [Fintype V] in
lemma flowCircuit_of_cycle (hN : N.Simple) (x : E → ℝ)
    (hx : N.boundary x = 0) (hs : N.flowSupport x = N.cycleEdges C) : N.FlowCircuit x := by
  have hcs : (N.cycleEdges C).Nonempty := ⟨N.cycleEdge C 0, by simp⟩
  refine ⟨hx,?_,?_⟩
  · intro hz; subst x
    have he := (N.flowSupport_eq_empty_iff 0).mpr rfl
    rw [he] at hs
    exact hcs.ne_empty hs.symm
  · intro y hy hsub
    by_cases hzero : y = 0
    · exact Or.inl hzero
    · right
      rw [hs] at hsub ⊢
      exact N.cycle_support_minimal C hN y hy hsub hzero

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.flowCircuit_of_cycle := @_root_.OAI.Barnette.Network.flowCircuit_of_cycle
