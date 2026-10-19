-- Prove2me | solution 1 for OAI.Barnette.Network.region_cycles_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:37:16.456554+00:00
-- url     : https://prove2.me/submissions/cb8cda17-bf83-4ef4-9392-09eabe3fb307

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/DiskRegions.lean:L184-L238
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.region_cycles_eq_range. The node keeps its source
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

-- ---- from OAI.Combinatorics.Hamiltonian.Network ----
namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

variable [Fintype V] [Fintype E]
attribute [local instance] OAI.Barnette.Network.instDecidableEq
attribute [local instance] OAI.Barnette.Network.instDecidableEq_1
theorem boundary_adjoint (x : E → ℝ) (f : V → ℝ) :
    ∑ v, N.boundary x v * f v = ∑ e, x e * N.gradient f e := by
  classical
  simp only [boundary_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [sub_mul, ite_mul, Finset.sum_sub_distrib, mul_sub]

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

-- ---- from OAI.Combinatorics.Hamiltonian.Quotients ----
namespace OAI

/-! Vertex quotients and connected fibers of incidence networks. -/

namespace Barnette.Network
noncomputable section
variable {V W E K : Type*}
open scoped Classical

variable [Fintype V] [Fintype W] [Fintype E] [Fintype K]

lemma push_adjoint (q : V → W) (x : V → ℝ) (f : W → ℝ) :
    ∑ w, push q x w * f w = ∑ v, x v * pull q f v := by
  classical
  simp only [push_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

lemma eq_of_dot_eq (x y : V → ℝ)
    (h : ∀ f : V → ℝ, ∑ v, x v * f v = ∑ v, y v * f v) : x = y := by
  ext v
  have hh := h (fun w => if w = v then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using hh

lemma boundary_mapVertices (N : Network V E) (q : V → W) (x : E → ℝ) :
    (N.mapVertices q).boundary x = push q (N.boundary x) := by
  apply eq_of_dot_eq
  intro f
  rw [(N.mapVertices q).boundary_adjoint, N.gradient_mapVertices,
    push_adjoint, N.boundary_adjoint]

lemma boundary_restrict (N : Network V E) (j : K → E) (x : K → ℝ) :
    (N.restrict j).boundary x = N.boundary (push j x) := by
  apply eq_of_dot_eq
  intro f
  rw [(N.restrict j).boundary_adjoint, N.gradient_restrict,
    N.boundary_adjoint, push_adjoint]

omit [Fintype E] in
lemma pull_push_injective {j : K → E} (hj : Function.Injective j) (x : K → ℝ) :
    pull j (push j x) = x := by
  classical
  ext k
  simp [hj.eq_iff]

omit [Fintype E] in
lemma push_eq_zero_outside {j : K → E} (x : K → ℝ) {e : E} (he : e ∉ Set.range j) :
    push j x e = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  have hk : j k ≠ e := fun h => he ⟨k, h⟩
  simp [hk]

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.DiskRegions ----
namespace OAI

/-! Connected face regions and the exact disk Euler formula. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
lemma region_map (A : Finset V) :
    (N.region D A).mapVertices Subtype.val = D.restrict (Subtype.val : N.regionEdges A → E) := rfl

omit [Fintype V] in
lemma region_boundary (A : Finset V) (x : N.regionEdges A → ℝ) :
    push (Subtype.val : N.regionVertices D A → F) ((N.region D A).boundary x) =
      D.boundary (push Subtype.val x) := by
  rw [← boundary_mapVertices, N.region_map, boundary_restrict]

omit [Fintype V] in
lemma push_subtype_apply (A : Finset V) (f : A → ℝ) (v : A) :
    push (Subtype.val : A → V) f v.val = f v := by
  have h := congrFun (pull_push_injective (E := V) Subtype.val_injective f) v
  exact h

omit [Fintype V] in
lemma push_subtype_outside (A : Finset V) (f : A → ℝ) {v : V} (hv : v ∉ A) :
    push (Subtype.val : A → V) f v = 0 :=
  push_eq_zero_outside f (by simpa using hv)

omit [Fintype V] in
lemma extend_gradient_outside (A : Finset V) (f : A → ℝ) {e : E}
    (he : e ∉ N.regionEdges A) : N.gradient (push (Subtype.val : A → V) f) e = 0 := by
  have hh : N.head e ∉ A := fun h => he ((N.mem_regionEdges A e).mpr (Or.inr h))
  have ht : N.tail e ∉ A := fun h => he ((N.mem_regionEdges A e).mpr (Or.inl h))
  simp only [gradient_apply, push_subtype_outside A f hh, push_subtype_outside A f ht, sub_self]

omit [Fintype V] in
lemma extend_restrict_gradient (A : Finset V) (f : A → ℝ) :
    push (Subtype.val : N.regionEdges A → E)
      (pull Subtype.val (N.gradient (push (Subtype.val : A → V) f))) =
        N.gradient (push (Subtype.val : A → V) f) := by
  ext e
  by_cases he : e ∈ N.regionEdges A
  · exact push_subtype_apply (N.regionEdges A) _ ⟨e,he⟩
  · rw [push_subtype_outside (N.regionEdges A) _ he]
    exact (N.extend_gradient_outside A f he).symm

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
lemma region_cycles_eq_range (h : N.Duality D) (A : Finset V)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected) :
    (N.region D A).boundary.ker = (N.regionCycleMap A).range := by
  ext x
  constructor
  · intro hx
    have hx' : (N.region D A).boundary x = 0 := hx
    let y : E → ℝ := push (Subtype.val : N.regionEdges A → E) x
    have hy : D.boundary y = 0 := by
      rw [← N.region_boundary D A x, hx',map_zero]
    obtain ⟨f,hf⟩ : ∃ f, N.gradient f = y := by
      have hm : y ∈ D.boundary.ker := hy
      rw [h.dual_cycles_eq_cuts] at hm
      exact hm
    obtain ⟨r⟩ := hAc.nonempty
    have fstep {v w : {v // v ∉ A}}
        (hvw : (N.graph.induce {v | v ∉ A}).Adj v w) : f v.val = f w.val := by
      obtain ⟨_,e,he⟩ := hvw
      have heA : e ∉ N.regionEdges A := by
        rw [N.mem_regionEdges]
        exact he.elim (fun he => by rw [he.1,he.2]; exact not_or.mpr ⟨v.property,w.property⟩)
          (fun he => by rw [he.1,he.2]; exact not_or.mpr ⟨w.property,v.property⟩)
      have hy0 : y e = 0 := push_eq_zero_outside x (by simpa using heA)
      have heq := congrFun hf e
      rw [hy0,gradient_apply,sub_eq_zero] at heq
      exact he.elim (fun he => by rw [he.1,he.2] at heq; exact heq.symm)
        (fun he => by rwa [he.1,he.2] at heq)
    have fconstant (v : {v // v ∉ A}) : f v.val = f r.val := by
      obtain ⟨p⟩ := hAc v r
      induction p with
      | nil => rfl
      | cons h p ih => exact (fstep h).trans ih
    let u : A → ℝ := fun v => f v.val - f r.val
    have hext : push (Subtype.val : A → V) u = f - (fun _ => f r.val) := by
      ext v
      by_cases hv : v ∈ A
      · exact push_subtype_apply A u ⟨v,hv⟩
      · rw [push_subtype_outside A u hv]
        exact (sub_eq_zero.mpr (fconstant ⟨v,hv⟩)).symm
    refine ⟨u,?_⟩
    change pull (Subtype.val : N.regionEdges A → E) (N.gradient (push Subtype.val u)) = x
    rw [hext,map_sub,N.gradient_const,sub_zero,hf]
    exact pull_push_injective Subtype.val_injective x
  · rintro ⟨f,rfl⟩
    have hz : push (Subtype.val : N.regionVertices D A → F)
        ((N.region D A).boundary (N.regionCycleMap A f)) = 0 := by
      rw [N.region_boundary]
      change D.boundary (push (Subtype.val : N.regionEdges A → E)
        (pull Subtype.val (N.gradient (push (Subtype.val : A → V) f)))) = 0
      rw [N.extend_restrict_gradient]
      exact h.dual_conserved_gradient N D _
    have hh := congrArg (pull (Subtype.val : N.regionVertices D A → F)) hz
    rw [pull_push_injective Subtype.val_injective,map_zero] at hh
    exact hh

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


theorem solution : type_of% @_root_.OAI.Barnette.Network.region_cycles_eq_range := @_root_.OAI.Barnette.Network.region_cycles_eq_range
