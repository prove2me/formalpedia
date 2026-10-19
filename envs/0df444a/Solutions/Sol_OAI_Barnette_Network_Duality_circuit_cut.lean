-- Prove2me | solution 1 for OAI.Barnette.Network.Duality.circuit_cut
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:24:31.026308+00:00
-- url     : https://prove2.me/submissions/f099ebe1-f2b9-435e-8a6c-316b632f0a36

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/FlowCircuits.lean:L73-L127
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Duality.circuit_cut. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits

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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

omit [Fintype V] [Fintype F] in

theorem Duality.circuit_two_levels (h : N.Duality D) (x : E → ℝ)
    (hx : D.FlowCircuit x) (f : V → ℝ) (hf : N.gradient f = x)
    {e : E} (he : x e ≠ 0) :
    ∀ v, f v = f (N.tail e) ∨ f v = f (N.head e) := by
  have he' : f (N.head e) ≠ f (N.tail e) := by
    simpa only [← hf, gradient_apply, sub_ne_zero] using he
  intro v
  by_contra hv
  obtain ⟨hvt,hvh⟩ := not_or.mp hv
  let g : V → ℝ := fun w => if f w = f v then 1 else 0
  have hgsub : D.flowSupport (N.gradient g) ⊆ D.flowSupport x := by
    intro k hk
    apply (D.mem_flowSupport x k).mpr
    intro hxk
    have hfk : f (N.head k) = f (N.tail k) := by
      apply sub_eq_zero.mp
      simpa only [← hf, gradient_apply] using hxk
    have hgk : N.gradient g k = 0 := by simp only [gradient_apply, g, hfk, sub_self]
    exact (D.mem_flowSupport _ k).mp hk hgk
  have hg : N.gradient g ≠ 0 := by
    intro hg
    have hh := N.gradient_zero_reachable hg (h.connected v (N.tail e))
    have htv : f (N.tail e) ≠ f v := Ne.symm hvt
    norm_num [g,htv] at hh
  have hgs := (hx.minimal (N.gradient g) (h.dual_conserved_gradient N D g) hgsub).resolve_left hg
  have hek : N.gradient g e ≠ 0 := (D.mem_flowSupport _ e).mp (by
    rw [hgs]; exact (D.mem_flowSupport _ e).mpr he)
  have htv : f (N.tail e) ≠ f v := Ne.symm hvt
  have hhv : f (N.head e) ≠ f v := Ne.symm hvh
  exact hek (by simp [gradient_apply, g, htv, hhv])

omit [Fintype F] in

theorem Duality.circuit_cut (h : N.Duality D) (x : E → ℝ)
    (hx : D.FlowCircuit x) (root : V) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ c ≠ 0 ∧
      x = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.flowSupport x := by
  obtain ⟨f,hf⟩ := h.gradient_of_dual_conserved N D hx.conserved
  obtain ⟨e,he⟩ : ∃ e, x e ≠ 0 := by
    by_contra hn
    apply hx.nonzero
    ext e
    exact not_not.mp (fun he => hn ⟨e,he⟩)
  have he' : f (N.head e) ≠ f (N.tail e) := by
    simpa only [← hf, gradient_apply, sub_ne_zero] using he
  have hall := h.circuit_two_levels N D x hx f hf he
  let a := f root
  let b := if a = f (N.tail e) then f (N.head e) else f (N.tail e)
  have hab : b ≠ a := by
    dsimp [b,a]
    split_ifs with ha
    · rw [ha]; exact he'
    · exact Ne.symm ha
  have hlevels (v : V) : f v = a ∨ f v = b := by
    dsimp [b,a] at ⊢
    rcases hall root with ht | hh
    · rw [ite_eq_left ht,ht]; exact hall v
    · have ht : f root ≠ f (N.tail e) := hh ▸ he'
      rw [ite_eq_right ht,hh]
      exact (hall v).symm
  have hb : ∃ v, f v = b := by
    dsimp [b]
    split_ifs
    · exact ⟨N.head e,rfl⟩
    · exact ⟨N.tail e,rfl⟩
  let A := Finset.univ.filter fun v => f v = b
  have fform (v : V) : f v = a + (b-a) * (if v ∈ A then 1 else 0) := by
    rcases hlevels v with hv | hv
    · have hvA : v ∉ A := by simp [A,hv,Ne.symm hab]
      simp [hvA,hv]
    · have hvA : v ∈ A := by simp [A,hv]
      simp [hvA,hv]
  refine ⟨A,b-a,?_,?_,sub_ne_zero.mpr hab,?_,?_⟩
  · obtain ⟨v,hv⟩ := hb; exact ⟨v,by simp [A,hv]⟩
  · simp [A,show f root = a from rfl, Ne.symm hab]
  · rw [← hf]
    ext k
    simp only [gradient_apply, Pi.smul_apply, smul_eq_mul]
    rw [fform (N.head k), fform (N.tail k)]
    ring
  · ext k
    simp only [mem_cut, mem_flowSupport, ← hf, gradient_apply, sub_ne_zero]
    rw [fform (N.head k), fform (N.tail k)]
    by_cases ht : N.tail k ∈ A <;> by_cases hh : N.head k ∈ A <;>
      simp [ht,hh,hab,Ne.symm hab]

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

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.Duality.circuit_cut := @_root_.OAI.Barnette.Network.Duality.circuit_cut
