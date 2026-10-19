-- Prove2me | solution 1 for OAI.Barnette.Network.Duality.bond_of_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:28:26.159526+00:00
-- url     : https://prove2.me/submissions/e46dd1cb-7786-46cb-9030-c6841733d684

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Bonds.lean:L111-L127
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Duality.bond_of_circuit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds

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

omit [Fintype V] [Fintype F] in
lemma Duality.dual_conserved_gradient (h : N.Duality D) (f : V → ℝ) :
    D.boundary (N.gradient f) = 0 := by
  have hh : N.gradient f ∈ N.gradient.range := ⟨f,rfl⟩
  rwa [← h.dual_cycles_eq_cuts] at hh

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

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Bonds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cycle flows, minimal cuts, and connected shores. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma support_cut (A : Finset V) :
    D.flowSupport (N.gradient (fun v => if v ∈ A then 1 else 0)) = N.cut A := by
  ext e
  simp only [mem_flowSupport,mem_cut,gradient_apply]
  by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;> simp [ht,hh]

omit [Fintype V] [Fintype F] in
lemma Duality.bond_of_circuit (h : N.Duality D) (x : E → ℝ) (hx : D.FlowCircuit x)
    (A : Finset V) (hA : N.cut A = D.flowSupport x) : N.Bond A := by
  refine ⟨?_,?_⟩
  · rw [hA]
    apply Finset.nonempty_iff_ne_empty.mpr
    exact fun he => hx.nonzero ((D.flowSupport_eq_empty_iff x).mp he)
  · intro B hB
    let y := N.gradient (fun v => if v ∈ B then 1 else 0)
    have hy : D.flowSupport y = N.cut B := N.support_cut D B
    have hys : D.flowSupport y ⊆ D.flowSupport x := by rwa [hy,← hA]
    rcases hx.minimal y (h.dual_conserved_gradient N D _) hys with hzero | heq
    · left
      rw [← hy]
      exact (D.flowSupport_eq_empty_iff y).mpr hzero
    · right
      rwa [hy,← hA] at heq

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.Duality.bond_of_circuit := @_root_.OAI.Barnette.Network.Duality.bond_of_circuit
