-- Prove2me | solution 1 for OAI.Barnette.Network.connected_of_kernel_constants
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:11:06.978203+00:00
-- url     : https://prove2.me/submissions/34b9076b-42d4-472c-9060-48140fe8143d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Forest.lean:L248-L264
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.connected_of_kernel_constants. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.Network ----
namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

theorem edge_reachable (e : E) : N.graph.Reachable (N.tail e) (N.head e) := by
  by_cases h : N.tail e = N.head e
  · rw [h]
  · exact (show N.graph.Adj (N.tail e) (N.head e) from
      ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩).reachable

theorem gradient_eq_zero_iff (f : V → ℝ) :
    N.gradient f = 0 ↔ ∀ e, f (N.head e) = f (N.tail e) := by
  simp only [funext_iff, gradient_apply, Pi.zero_apply, sub_eq_zero]

variable [Fintype V] [Fintype E]
attribute [local instance] OAI.Barnette.Network.instDecidableEq
attribute [local instance] OAI.Barnette.Network.instDecidableEq_1
variable {F : Type*} [Fintype F] (D : Network F E)

end
end Network
end Barnette

namespace Barnette
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

end
end Barnette

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Forest ----
namespace OAI

/-! Common-phase nonvanishing and forest extraction from actual states. -/

namespace Barnette
noncomputable section
open scoped Classical

namespace TriangleSystem.Pair
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

variable [Fintype A]

end TriangleSystem.Pair
end
end Barnette
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
omit [Fintype V] [Fintype E] in
lemma connected_of_kernel_constants [Nonempty V]
    (hc : ∀ f : V → ℝ, N.gradient f = 0 → ∀ v w, f v = f w) : N.graph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, inferInstance⟩
  intro v w
  by_contra hw
  let f : V → ℝ := fun z => if N.graph.Reachable v z then 1 else 0
  have hf : N.gradient f = 0 := by
    apply (N.gradient_eq_zero_iff f).mpr
    intro e
    have he := N.edge_reachable e
    have hh : N.graph.Reachable v (N.head e) ↔ N.graph.Reachable v (N.tail e) :=
      ⟨fun h => h.trans he.symm, fun h => h.trans he⟩
    simp only [f, hh]
  have he := hc f hf v w
  simp [f, hw] at he

variable {F : Type*} [Fintype F]
end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.connected_of_kernel_constants := @_root_.OAI.Barnette.Network.connected_of_kernel_constants
