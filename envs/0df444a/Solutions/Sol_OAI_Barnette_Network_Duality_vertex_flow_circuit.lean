-- Prove2me | solution 1 for OAI.Barnette.Network.Duality.vertex_flow_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:41:45.490792+00:00
-- url     : https://prove2.me/submissions/4ce24f89-a820-4518-8e61-e75d9db739ea

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean:L21-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Duality.vertex_flow_circuit. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.Network ----
namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

theorem gradient_eq_zero_iff (f : V → ℝ) :
    N.gradient f = 0 ↔ ∀ e, f (N.head e) = f (N.tail e) := by
  simp only [funext_iff, gradient_apply, Pi.zero_apply, sub_eq_zero]

theorem gradient_zero_adj {f : V → ℝ} (hf : N.gradient f = 0)
    {v w : V} (h : N.graph.Adj v w) : f v = f w := by
  obtain ⟨_, e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact ((N.gradient_eq_zero_iff f).mp hf e).symm
  · exact (N.gradient_eq_zero_iff f).mp hf e

theorem gradient_zero_reachable {f : V → ℝ} (hf : N.gradient f = 0)
    {v w : V} (h : N.graph.Reachable v w) : f v = f w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (N.gradient_zero_adj hf h).trans ih

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

-- ---- from OAI.Combinatorics.Hamiltonian.FlowCircuits ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Minimal flow circuits, triangular faces, and simple cycle coordinates. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma Duality.dual_conserved_gradient (h : N.Duality D) (f : V → ℝ) :
    D.boundary (N.gradient f) = 0 := by
  have hh : N.gradient f ∈ N.gradient.range := ⟨f,rfl⟩
  rwa [← h.dual_cycles_eq_cuts] at hh

omit [Fintype V] [Fintype F] in
lemma Duality.gradient_of_dual_conserved (h : N.Duality D) {x : E → ℝ}
    (hx : D.boundary x = 0) : ∃ f, N.gradient f = x := by
  have hh : x ∈ D.boundary.ker := hx
  rwa [h.dual_cycles_eq_cuts] at hh

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

-- ---- from OAI.Combinatorics.Hamiltonian.StateDisk ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Minimal links, incidence states, and the signed disk identity. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma Duality.symm (h : N.Duality D) : D.Duality N :=
  ⟨h.dual_connected,h.connected,h.dual_cycles_eq_cuts,h.cycles_eq_cuts⟩

omit [Fintype V] [Fintype F] in

lemma Duality.vertex_flow_circuit (h : N.Duality D) (z : F)
    (hz : (D.graph.induce {v | v ≠ z}).Connected) :
    N.FlowCircuit (D.gradient (fun w => if w = z then 1 else 0)) := by
  obtain ⟨r⟩ := hz.nonempty
  let x := D.gradient (fun w => if w = z then (1:ℝ) else 0)
  have hx : N.boundary x = 0 := (h.symm N D).dual_conserved_gradient D N _
  have hn : x ≠ 0 := by
    intro he
    have hh := D.gradient_zero_reachable he (h.dual_connected z r.val)
    norm_num at hh
    exact r.property hh
  refine ⟨hx,hn,?_⟩
  intro y hy hs
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  right
  obtain ⟨f,hf⟩ := (h.symm N D).gradient_of_dual_conserved D N hy
  have fstep {v w : {v // v ≠ z}}
      (hvw : (D.graph.induce {v | v ≠ z}).Adj v w) : f v.val = f w.val := by
    obtain ⟨_,e,he⟩ := hvw
    have hxe : x e = 0 := by
      dsimp only [x,gradient_apply]
      rcases he with he | he <;> rw [he.1,he.2] <;> simp [v.property,w.property]
    have hye : y e = 0 := by
      by_contra he
      exact (N.mem_flowSupport x e).mp (hs ((N.mem_flowSupport y e).mpr he)) hxe
    have heq := congrFun hf e
    rw [hye,gradient_apply,sub_eq_zero] at heq
    exact he.elim (fun he => by rw [he.1,he.2] at heq; exact heq.symm)
      (fun he => by rwa [he.1,he.2] at heq)
  have fconstant (v : {v // v ≠ z}) : f v.val = f r.val := by
    obtain ⟨p⟩ := hz v r
    induction p with
    | nil => rfl
    | cons h p ih => exact (fstep h).trans ih
  have hne : f z ≠ f r.val := by
    intro he
    apply hy0
    rw [← hf]
    apply (D.gradient_eq_zero_iff f).mpr
    have hall (v : F) : f v = f r.val := by
      by_cases hv : v = z
      · rwa [hv]
      · exact fconstant ⟨v,hv⟩
    intro e
    exact (hall _).trans (hall _).symm
  apply Finset.Subset.antisymm hs
  intro e he
  apply (N.mem_flowSupport y e).mpr
  rw [← hf,gradient_apply]
  have hxe := (N.mem_flowSupport x e).mp he
  dsimp only [x,gradient_apply] at hxe
  by_cases ht : D.tail e = z <;> by_cases hh : D.head e = z
  · simp [ht,hh] at hxe
  · rw [ht,fconstant ⟨D.head e,hh⟩]
    exact sub_ne_zero.mpr hne.symm
  · rw [hh,fconstant ⟨D.tail e,ht⟩]
    exact sub_ne_zero.mpr hne
  · simp [ht,hh] at hxe

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

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


theorem solution : type_of% @_root_.OAI.Barnette.Network.Duality.vertex_flow_circuit := @_root_.OAI.Barnette.Network.Duality.vertex_flow_circuit
