-- Prove2me | solution 1 for OAI.Barnette.Network.Bond.connected_shore
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:30:10.365018+00:00
-- url     : https://prove2.me/submissions/45adb16c-861e-4c2b-afac-f8ede9983c46

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Bonds.lean:L164-L201
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Bond.connected_shore. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds

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

omit [Fintype V] in
lemma cuts_equal_subset (h : N.graph.Connected) {A B : Finset V} (hBA : B ⊆ A)
    (hout : ∃ v, v ∉ A) (hc : N.cut B = N.cut A) : B = A := by
  let f : V → ℝ := fun v => (if v ∈ A then 1 else 0) - (if v ∈ B then 1 else 0)
  have hf : N.gradient f = 0 := by
    ext e
    have he := Finset.ext_iff.mp hc e
    simp only [mem_cut] at he
    have ht := hBA (x := N.tail e)
    have hh := hBA (x := N.head e)
    dsimp only [gradient_apply,f,Pi.zero_apply]
    by_cases hta : N.tail e ∈ A <;> by_cases hha : N.head e ∈ A <;>
      by_cases htb : N.tail e ∈ B <;> by_cases hhb : N.head e ∈ B <;>
      simp_all
  obtain ⟨r,hr⟩ := hout
  have hrB : r ∉ B := fun h => hr (hBA h)
  apply Finset.Subset.antisymm hBA
  intro v hv
  have hh := N.gradient_zero_reachable hf (h r v)
  by_contra hvB
  norm_num [f,hr,hrB,hv,hvB] at hh

omit [Fintype V] in
lemma cut_nonempty (h : N.graph.Connected) (A : Finset V) (hin : A.Nonempty)
    (hout : ∃ v, v ∉ A) : (N.cut A).Nonempty := by
  by_contra hc
  have hc' : N.cut A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
  have hf : N.gradient (fun v => if v ∈ A then (1:ℝ) else 0) = 0 := by
    apply (N.flowSupport_eq_empty_iff _).mp
    rwa [N.support_cut N A]
  obtain ⟨v,hv⟩ := hin
  obtain ⟨w,hw⟩ := hout
  have hh := N.gradient_zero_reachable hf (h v w)
  norm_num [hv,hw] at hh

omit [Fintype V] in

lemma Bond.connected_shore (h : N.graph.Connected) {A : Finset V} (hA : N.Bond A)
    (hin : A.Nonempty) (hout : ∃ v, v ∉ A) :
    (N.graph.induce {v | v ∈ A}).Connected := by
  obtain ⟨a,ha⟩ := hin
  let H := N.graph.induce {v | v ∈ A}
  let B := A.filter fun v => ∃ hv : v ∈ A, H.Reachable ⟨a,ha⟩ ⟨v,hv⟩
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have haB : a ∈ B := Finset.mem_filter.mpr ⟨ha,ha,SimpleGraph.Reachable.refl _⟩
  have hsub : N.cut B ⊆ N.cut A := by
    intro e he
    have step {v w : V} (hv : v ∈ B) (hw : w ∈ A) (hvw : N.graph.Adj v w) : w ∈ B := by
      obtain ⟨hvA,hvR⟩ := Finset.mem_filter.mp hv
      obtain ⟨hv',hp⟩ := hvR
      exact Finset.mem_filter.mpr ⟨hw,hw,hp.trans (show H.Adj ⟨v,hv'⟩ ⟨w,hw⟩ from hvw).reachable⟩
    rcases (N.mem_cut B e).mp he with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · apply (N.mem_cut A e).mpr
      refine Or.inl ⟨hBA ht,?_⟩
      intro hha
      have hne : N.tail e ≠ N.head e := fun heq => hh (heq ▸ ht)
      exact hh (step ht hha ⟨hne,e,Or.inl ⟨rfl,rfl⟩⟩)
    · apply (N.mem_cut A e).mpr
      refine Or.inr ⟨hBA hh,?_⟩
      intro hta
      have hne : N.head e ≠ N.tail e := fun heq => ht (heq ▸ hh)
      exact ht (step hh hta ⟨hne,e,Or.inr ⟨rfl,rfl⟩⟩)
  have hBout : ∃ v, v ∉ B := by
    obtain ⟨r,hr⟩ := hout
    exact ⟨r,fun h => hr (hBA h)⟩
  have hc := (hA.minimal B hsub).resolve_left (N.cut_nonempty h B ⟨a,haB⟩ hBout).ne_empty
  have hEq := N.cuts_equal_subset h hBA hout hc
  apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
  refine ⟨⟨a,ha⟩,?_⟩
  intro v
  have hvB : v.val ∈ B := by rw [hEq]; exact v.property
  obtain ⟨_,hv,hp⟩ := Finset.mem_filter.mp hvB
  exact hp

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


theorem solution : type_of% @_root_.OAI.Barnette.Network.Bond.connected_shore := @_root_.OAI.Barnette.Network.Bond.connected_shore
