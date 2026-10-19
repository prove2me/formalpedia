-- Prove2me | solution 1 for OAI.Barnette.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:24:31.152995+00:00
-- url     : https://prove2.me/submissions/ef6232e5-4ab4-4b8f-96f2-07cf48ae6d0d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Main.lean:L47-L82
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Barnette.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Barnette_main) verbatim and is proved by it.
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_SquareGrid
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Corridors
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorModel
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Rectangle
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ExactDual
import Theorems.Thm_OAI_Barnette_BranchPartition_extend
import Theorems.Thm_OAI_Barnette_BranchPartition_quotient
import Theorems.Thm_OAI_Barnette_Network_Bond_connected_shore
import Theorems.Thm_OAI_Barnette_Network_ColoredDual_StateCycle_signed
import Theorems.Thm_OAI_Barnette_Network_ColoredDual_pair_nonempty
import Theorems.Thm_OAI_Barnette_Network_ColoredDual_recover_connected_complement
import Theorems.Thm_OAI_Barnette_Network_Duality_minor
import Theorems.Thm_OAI_Barnette_Network_Duality_simple_dual_edge
import Theorems.Thm_OAI_Barnette_Network_ThreeEdgeConnected_connected
import Theorems.Thm_OAI_Barnette_Network_boundary_of_sum_zero
import Theorems.Thm_OAI_Barnette_Network_cap_coloring
import Theorems.Thm_OAI_Barnette_Network_cap_connectedFibers
import Theorems.Thm_OAI_Barnette_Network_cap_star_none
import Theorems.Thm_OAI_Barnette_Network_cap_star_some
import Theorems.Thm_OAI_Barnette_Network_card_star
import Theorems.Thm_OAI_Barnette_Network_nontrivial_threeCut
import Theorems.Thm_OAI_Barnette_Network_oriented_face
import Theorems.Thm_OAI_Barnette_Network_simple_of_cubic_stars
import Theorems.Thm_OAI_Barnette_Network_triangle_of_flow
import Theorems.Thm_OAI_Barnette_PlaneEmbedding_exists_lattice_corridor_model
import Theorems.Thm_OAI_Barnette_SimpleCycle_cycle_at_of_connected_two
import Theorems.Thm_OAI_Barnette_SimpleCycle_delete_vertex_connected
import Theorems.Thm_OAI_Barnette_TriangleSystem_Pair_forest_pair_of_disk_circulation
import Theorems.Thm_OAI_Barnette_boundary_cover_of_threeConnected

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

theorem ker_gradient (h : N.graph.Connected) :
    N.gradient.ker = (constant (V := V)).range := by
  obtain ⟨v⟩ := h.nonempty
  ext f
  constructor
  · intro hf
    refine ⟨f v, ?_⟩
    ext w
    exact N.gradient_zero_reachable hf (h v w)
  · rintro ⟨a, rfl⟩
    exact N.gradient_const a

variable [Fintype V] [Fintype E]
attribute [local instance] OAI.Barnette.Network.instDecidableEq
attribute [local instance] OAI.Barnette.Network.instDecidableEq_1
omit [Fintype E] in
theorem gradient_matrix : N.gradient = Matrix.toLin' N.incidence.transpose := by
  classical
  apply LinearMap.ext
  intro f
  ext e
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, incidence,
    sub_mul, ite_mul, Finset.sum_sub_distrib]

omit [Fintype E] in
theorem rank_gradient (h : N.graph.Connected) :
    Module.finrank ℝ N.gradient.range + 1 = Fintype.card V := by
  obtain ⟨v⟩ := h.nonempty
  have hi : Function.Injective (constant (V := V)) := by
    intro a b hab
    exact congrFun hab v
  have hk : Module.finrank ℝ N.gradient.ker = 1 := by
    rw [N.ker_gradient h, LinearMap.finrank_range_of_inj hi]
    exact Module.finrank_self ℝ
  have hh := N.gradient.finrank_range_add_finrank_ker
  simpa only [hk, Module.finrank_pi] using hh

theorem rank_boundary (h : N.graph.Connected) :
    Module.finrank ℝ N.boundary.range + 1 = Fintype.card V := by
  have hh := N.rank_gradient h
  have he : Module.finrank ℝ N.boundary.range = Module.finrank ℝ N.gradient.range := by
    rw [N.gradient_matrix, boundary, Matrix.toLin'_apply', Matrix.toLin'_apply',
      ← Matrix.rank, ← Matrix.rank, Matrix.rank_transpose]
  rwa [he]

theorem dim_cycles (h : N.graph.Connected) :
    Module.finrank ℝ N.boundary.ker + Fintype.card V = Fintype.card E + 1 := by
  have hr := N.rank_boundary h
  have hk := N.boundary.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hk
  omega

theorem boundary_adjoint (x : E → ℝ) (f : V → ℝ) :
    ∑ v, N.boundary x v * f v = ∑ e, x e * N.gradient f e := by
  classical
  simp only [boundary_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [sub_mul, ite_mul, Finset.sum_sub_distrib, mul_sub]

variable {F : Type*} [Fintype F] (D : Network F E)

theorem orthogonal_symm (h : ∀ f, N.boundary (D.gradient f) = 0) :
    ∀ f, D.boundary (N.gradient f) = 0 := by
  classical
  intro f
  ext y
  calc
    D.boundary (N.gradient f) y =
        ∑ z, D.boundary (N.gradient f) z * (fun z : F => if z = y then (1 : ℝ) else 0) z := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = ∑ e, N.gradient f e * D.gradient ((fun z : F => if z = y then (1 : ℝ) else 0)) e :=
      D.boundary_adjoint _ _
    _ = ∑ e, D.gradient ((fun z : F => if z = y then (1 : ℝ) else 0)) e * N.gradient f e := by
      apply Finset.sum_congr rfl
      intro e _
      exact mul_comm _ _
    _ = ∑ v, N.boundary (D.gradient ((fun z : F => if z = y then (1 : ℝ) else 0))) v * f v :=
      (N.boundary_adjoint _ _).symm
    _ = 0 := by rw [h]; simp

private theorem ker_eq_range_of_orth_card
    (hN : N.graph.Connected) (hD : D.graph.Connected)
    (hc : Fintype.card V + Fintype.card F = Fintype.card E + 2)
    (ho : ∀ f, N.boundary (D.gradient f) = 0) :
    N.boundary.ker = D.gradient.range := by
  have hle : D.gradient.range ≤ N.boundary.ker := by
    rintro _ ⟨f, rfl⟩
    exact ho f
  have hd₁ := N.dim_cycles hN
  have hd₂ := D.rank_gradient hD
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem duality_of_orth_card
    (hN : N.graph.Connected) (hD : D.graph.Connected)
    (hc : Fintype.card V + Fintype.card F = Fintype.card E + 2)
    (ho : ∀ f, N.boundary (D.gradient f) = 0) : N.Duality D where
  connected := hN
  dual_connected := hD
  cycles_eq_cuts := N.ker_eq_range_of_orth_card D hN hD hc ho
  dual_cycles_eq_cuts := D.ker_eq_range_of_orth_card N hD hN (by omega)
    (N.orthogonal_symm D ho)

end
end Network
end Barnette

namespace Barnette
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma cubic_bipartite_order [Nonempty V] (hc : G.IsRegularOfDegree 3)
    (hb : G.IsBipartite) : 6 ≤ Fintype.card V := by
  obtain ⟨c⟩ := hb
  obtain ⟨v⟩ := ‹Nonempty V›
  have hp : (G.neighborFinset v).Nonempty := by
    apply Finset.card_pos.mp
    rw [G.card_neighborFinset_eq_degree, hc v]
    norm_num
  obtain ⟨w, hw⟩ := hp
  have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hd : Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have h₁ := c.valid hvw
    have h₂ := c.valid ((G.mem_neighborFinset v x).mp hx)
    have h₃ := c.valid ((G.mem_neighborFinset w x).mp hy)
    have hv := (c v).isLt
    have hw := (c w).isLt
    have hx := (c x).isLt
    have h₁' : (c v).val ≠ (c w).val := fun h => h₁ (Fin.ext h)
    have h₂' : (c v).val ≠ (c x).val := fun h => h₂ (Fin.ext h)
    have h₃' : (c w).val ≠ (c x).val := fun h => h₃ (Fin.ext h)
    omega
  have hle := Finset.card_le_card (Finset.subset_univ
    (G.neighborFinset v ∪ G.neighborFinset w))
  rw [Finset.card_union_of_disjoint hd, G.card_neighborFinset_eq_degree,
    G.card_neighborFinset_eq_degree, hc v, hc w, Finset.card_univ] at hle
  exact hle

end
end Barnette

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.CutSpaces ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Cuts, simplicity, and connectivity of finite oriented networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma region_card_le_cut (h : ThreeVertexConnected N.graph)
    (A : Finset V) (hout : ∃ w, w ∉ A) (hc : (N.cut A).card ≤ 2) :
    A.card ≤ (N.cut A).card := by
  let p : E → V := fun e => if N.tail e ∈ A then N.tail e else N.head e
  let S := (N.cut A).image p
  have hS : S.card ≤ 2 := (Finset.card_image_le).trans hc
  have hSA : S ⊆ A := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    rcases (N.mem_cut A e).mp he with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · simpa only [p, ite_eq_left ht] using ht
    · simpa only [p, ite_eq_right ht] using hh
  have hsubset : A ⊆ S := by
    apply boundary_cover_of_threeConnected h A S hS hSA hout
    intro v hv w hw hvw
    obtain ⟨_, e, he⟩ := hvw
    apply Finset.mem_image.mpr
    rcases he with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · refine ⟨e, (N.mem_cut A e).mpr (Or.inl ?_), ?_⟩
      · simpa only [ht,hh] using And.intro hv hw
      · simp only [p, ht, hv, ite_true]
    · refine ⟨e, (N.mem_cut A e).mpr (Or.inr ?_), ?_⟩
      · simpa only [ht,hh] using And.intro hv hw
      · simp only [p, ht, hh, hw, ite_false]
  exact (Finset.card_le_card hsubset).trans Finset.card_image_le

lemma cut_card_three (h : ThreeVertexConnected N.graph)
    (hV : 5 ≤ Fintype.card V) (A : Finset V) (hin : A.Nonempty)
    (hout : ∃ w, w ∉ A) : 3 ≤ (N.cut A).card := by
  by_contra hc
  have hc' : (N.cut A).card ≤ 2 := by omega
  have ha := N.region_card_le_cut h A hout hc'
  have hccompl : (N.cut Aᶜ).card ≤ 2 := by simpa only [cut_compl] using hc'
  have hb := N.region_card_le_cut h Aᶜ (by
    obtain ⟨v,hv⟩ := hin; exact ⟨v, by simpa only [Finset.mem_compl, not_not] using hv⟩) hccompl
  rw [cut_compl] at hb
  have he := Finset.card_add_card_compl A
  omega

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

omit [Fintype V] [Fintype F] in
lemma gradient_indicator_support (h : N.Simple) (v : V) :
    D.flowSupport (N.gradient (fun w => if w = v then 1 else 0)) = N.star v := by
  ext e
  simp only [mem_flowSupport, mem_star, gradient_apply, Incident]
  have hne := h.loopless e
  by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp [ht,hh] at *

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

lemma Bond.compl {A : Finset V} (hA : N.Bond A) : N.Bond Aᶜ where
  nonempty := by simpa only [cut_compl] using hA.nonempty
  minimal B hB := by
    rw [cut_compl] at hB ⊢
    exact hA.minimal B hB

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

-- ---- from OAI.Combinatorics.Hamiltonian.StateDisk ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Minimal links, incidence states, and the signed disk identity. -/

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

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackEndpoint_spec (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    black (N.blackEndpoint black e) ∧ N.Incident e (N.blackEndpoint black e) := by
  by_cases ht : black (N.tail e)
  · simp only [blackEndpoint,ite_eq_left ht]; exact ⟨ht,Or.inl rfl⟩
  · simp only [blackEndpoint,ite_eq_right ht]
    exact ⟨not_not.mp (fun hh => ht ((hc e).mpr hh)),Or.inr rfl⟩

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

-- ---- from OAI.Combinatorics.Hamiltonian.Circulation ----
namespace OAI

/-! Oriented triangular faces and positive white-face charges. -/

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

lemma whiteCharge_sum (black : V → Prop) (root : V) :
    ∑ v, whiteCharge black root v = 0 := by
  simp only [whiteCharge,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [show (fun v => if black v then (0:ℝ) else 1) =
    (fun v => if ¬black v then 1 else 0) by ext v; by_cases hv : black v <;> simp [hv]]
  rw [Finset.sum_boole,sub_self]

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.TriangleSystem ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Triangle incidence states, opposite graphs, and oriented potentials. -/

namespace Barnette

namespace TriangleSystem

variable {A V : Type*} (T : TriangleSystem A V)

namespace State

variable {T} {X : Set V}

end State

theorem indexDelta_antisymm : ∀ i j : Fin 3, indexDelta i j = -indexDelta j i := by
  decide

end TriangleSystem
end Barnette
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.PairPhases ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Paired states, permutation cycle classes, and phase cancellation. -/

namespace Barnette

namespace TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

namespace OppositeCycle

variable {s : T.State X} (C : T.OppositeCycle s)

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette

variable {A : Type*}

theorem classOf_eq_iff (p : Equiv.Perm A) (a b : A) :
    classOf p a = classOf p b ↔ p.SameCycle a b := Quotient.eq

end Barnette

namespace Barnette.TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

namespace Pair

end Pair
end Barnette.TriangleSystem

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

lemma cycleCoordinates_faces (P : @Pair A V T X) (c : CycleClass P.next) (a : A)
    (ha : classOf P.next a = c) :
    Finset.univ.image (P.cycleCoordinates a).face = P.cycleFaces c := by
  ext b
  simp only [Finset.mem_image,Finset.mem_univ,true_and,mem_cycleFaces]
  change b ∈ Set.range (P.cycleCoordinates a).face ↔ _
  rw [(P.cycleCoordinates a).range_eq]
  change P.next.SameCycle a b ↔ _
  rw [← classOf_eq_iff,ha]
  exact eq_comm

end TriangleSystem.Pair
end
end Barnette
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

omit [Fintype F] in
lemma pairedCycle_delta (P : (M.system root).Pair (M.nonroots root))
    (c : Barnette.CycleClass P.next) (a : M.Black root) (ha : Barnette.classOf P.next a = c) :
    (M.pairedCycle P a).delta = P.cycleDelta c := by
  let : DecidableEq (M.Black root) := Classical.decEq _
  change (∑ i, indexDelta (P.left.val ((P.cycleCoordinates a).face i))
    (P.right.val ((P.cycleCoordinates a).face i))) =
      ∑ t ∈ P.cycleFaces c, indexDelta (P.left.val t) (P.right.val t)
  rw [← P.cycleCoordinates_faces c a ha]
  exact (Finset.sum_image (f := fun t => indexDelta (P.left.val t) (P.right.val t))
    (s := Finset.univ) (P.cycleCoordinates a).face.injective.injOn).symm

omit [Fintype F] in
lemma pairedCycle_slope (P : (M.system root).Pair (M.nonroots root))
    (c : Barnette.CycleClass P.next) (a : M.Black root) (ha : Barnette.classOf P.next a = c)
    (α : E → ℝ) :
    (M.pairedCycle P a).slope α = P.cycleSlope (M.weights α root) c := by
  let : DecidableEq (M.Black root) := Classical.decEq _
  change (∑ i, (M.weights α root ((P.cycleCoordinates a).face i)
    (P.right.val ((P.cycleCoordinates a).face i)) -
      M.weights α root ((P.cycleCoordinates a).face i)
        (P.left.val ((P.cycleCoordinates a).face i)))) =
      (∑ t ∈ P.cycleFaces c, M.weights α root t (P.right.val t)) -
        (∑ t ∈ P.cycleFaces c, M.weights α root t (P.left.val t))
  rw [← P.cycleCoordinates_faces c a ha,Finset.sum_sub_distrib]
  congr 1
  · exact (Finset.sum_image (f := fun t => M.weights α root t (P.right.val t))
      (s := Finset.univ) (P.cycleCoordinates a).face.injective.injOn).symm
  · exact (Finset.sum_image (f := fun t => M.weights α root t (P.left.val t))
      (s := Finset.univ) (P.cycleCoordinates a).face.injective.injOn).symm

lemma paired_sign (P : (M.system root).Pair (M.nonroots root))
    (c : Barnette.CycleClass P.next) (α : E → ℝ)
    (hα : N.boundary α = whiteCharge M.black root) :
    (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope (M.weights α root) c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope (M.weights α root) c < 0) := by
  obtain ⟨a,ha⟩ := Barnette.classOf_surjective P.next c
  have hh := (M.pairedCycle P a).signed α hα
  rwa [M.pairedCycle_delta P c a ha,M.pairedCycle_slope P c a ha α] at hh

omit [Fintype F] in
lemma oppositeForward_delta {s r : M.State root} (C : (M.system root).OppositeCycle s)
    (hrs : (M.system root).Partner r s)
    (hf : ∀ i, r.value (C.face i) = C.cycle.vertex i) :
    (M.oppositeForward C hrs hf).delta = C.cyclicDelta r := rfl

lemma opposite_disk {s : M.State root} (C : (M.system root).OppositeCycle s)
    (r : (M.system root).Partners s) (α : E → ℝ)
    (hα : N.boundary α = whiteCharge M.black root) :
    C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3 := by
  rcases C.partner_orientation r.property with hf | hb
  · have hs := (M.oppositeForward C r.property hf).signed α hα
    rw [M.oppositeForward_delta] at hs
    exact hs.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)
  · let r' := C.reverse r.val r.property
    have hrs' : (M.system root).Partner r' s := C.reverse_partner r.val r.property
    have hf : ∀ i, r'.value (C.face i) = C.cycle.vertex i := by
      intro i
      have hr : r'.value (C.face i) = (M.system root).vertex (C.face i)
          (thirdIndex (r.val.val (C.face i)) (s.val (C.face i))) := by
        change (M.system root).vertex _ (C.changedCorners r.val (C.face i)) = _
        rw [C.changedCorners_image]
      rw [hr]
      rcases C.partner_endpoints r.property i with ⟨he,_⟩ | ⟨_,he⟩
      · exact ((C.cycle.adjacent i).1 (he.symm.trans (hb i))).elim
      · exact he
    have hδ : C.cyclicDelta r' = -C.cyclicDelta r.val := by
      unfold OppositeCycle.cyclicDelta
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change indexDelta (C.changedCorners r.val (C.face i))
        (thirdIndex (C.changedCorners r.val (C.face i)) (s.val (C.face i))) = _
      rw [C.changedCorners_image,thirdIndex_involution,indexDelta_antisymm]
    have hs := (M.oppositeForward C hrs' hf).signed α hα
    rw [M.oppositeForward_delta,hδ] at hs
    rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩
    · left; omega
    · right; omega

theorem forest_pair (hex : Nonempty ((M.system root).Pair (M.nonroots root))) :
    ∃ P : (M.system root).Pair (M.nonroots root), ((M.system root).oppositeGraph P.right).IsAcyclic := by
  obtain ⟨α,hα⟩ := N.boundary_of_sum_zero M.duality.connected
    (whiteCharge M.black root) (whiteCharge_sum M.black root)
  exact Pair.forest_pair_of_disk_circulation hex
    (fun _ C r => M.opposite_disk C r α hα) (M.weights α root)
    (fun P c => M.paired_sign P c α hα)

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {F : Type*} [Fintype F]
end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Matching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Disk and spoke signs and matching complements. -/

namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
lemma Simple.restrict (hN : N.Simple) {K : Type*} (j : K → E) (hj : Function.Injective j) :
    (N.restrict j).Simple where
  loopless k := hN.loopless (j k)
  pair_injective _ _ h := hj (hN.pair_injective h)

variable {F : Type*} [Fintype F] (D : Network F E)
end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V A : Type*} (Q : Network V A)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
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
variable {V E : Type*} (D : Network V E)

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

end
end Barnette.Network.ColoredDual

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.ThreeCuts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Three-edge cuts, capped graphs, and preservation of graph properties. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)

omit [Fintype F] in
theorem Duality.cubic_face_triangles_edge (h : N.Duality D) (hN : N.Simple)
    (h3 : N.ThreeEdgeConnected)
    (hc : N.graph.IsRegularOfDegree 3) : ∀ v, Nonempty (D.Triangle (N.star v)) := by
  intro v
  have hD := h.simple_dual_edge N D h3
  have hx := h.dual_conserved_gradient N D (fun w => if w = v then 1 else 0)
  have hs : (D.flowSupport (N.gradient (fun w => if w = v then 1 else 0))).card = 3 := by
    rw [N.gradient_indicator_support D hN, N.card_star hN, hc v]
  simpa only [N.gradient_indicator_support D hN] using D.triangle_of_flow hD _ hx hs

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma make_coloredDual (h : N.Duality D) (hN : N.Simple) (h3 : N.ThreeEdgeConnected)
    (hc : N.graph.IsRegularOfDegree 3) (black : V → Prop)
    (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) : Nonempty (N.ColoredDual D) := by
  have hs := h.simple_dual_edge N D h3
  have ht := h.cubic_face_triangles_edge N D hN h3 hc
  choose t ho using fun v => N.oriented_face D h hN hs v (ht v).some
  exact ⟨⟨h,hN,hs,hc,black,hb,t,ho⟩⟩

lemma irreducible_matching (M : N.ColoredDual D)
    (h3 : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts) (e : E) :
    ∃ P : Finset E, e ∈ P ∧ (∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) ∧
      (N.restrict (Subtype.val : ↥(Pᶜ) → E)).graph.Connected := by
  let root := N.blackEndpoint M.black e
  have hr := (N.blackEndpoint_spec M.black M.coloring e).1
  have he : e ∈ N.star root := (N.mem_star _ _).mpr (N.blackEndpoint_spec M.black M.coloring e).2
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ((M.face root).edge_range.symm ▸ he)
  obtain ⟨Q,hQ⟩ := M.forest_pair (M.pair_nonempty h3 htr root hr)
  simpa only [hi] using M.recover_connected_complement Q hr hQ i
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype E] in
lemma capMap_surjective (A : Finset V) (hA : Aᶜ.Nonempty) : Function.Surjective (N.capMap A) := by
  rintro (_|v)
  · obtain ⟨v,hv⟩ := hA
    exact ⟨v,(N.capMap_eq_none A v).mpr (Finset.mem_compl.mp hv)⟩
  · exact ⟨v.val,N.capMap_some A v⟩

omit [Fintype V] in
lemma cap_loopless (hN : N.Simple) (A : Finset V) (e : N.regionEdges A) :
    (N.cap A).tail e ≠ (N.cap A).head e := by
  change N.capMap A (N.tail e.val) ≠ N.capMap A (N.head e.val)
  intro he
  rcases (N.mem_regionEdges A e.val).mp e.property with ht|hh
  · have ht' := N.capMap_some A ⟨N.tail e.val,ht⟩
    rw [ht'] at he
    exact hN.loopless e.val (((N.capMap_eq_some A _ _).mp he.symm).symm)
  · have hh' := N.capMap_some A ⟨N.head e.val,hh⟩
    rw [hh'] at he
    exact hN.loopless e.val ((N.capMap_eq_some A _ _).mp he)

lemma cap_star_card (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (A : Finset V) (hA : (N.cut A).card = 3) (v : Option A) : ((N.cap A).star v).card = 3 := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  cases v with
  | none => rw [N.cap_star_none,hA]
  | some v => rw [N.cap_star_some,N.card_star hN,hc v.val]

lemma cap_cut (A : Finset V) (B : Finset (Option A)) :
    ((N.cap A).cut B).image Subtype.val = N.cut (N.capPreimage A B) := by
  ext e
  simp only [Finset.mem_image,mem_cut,mem_capPreimage]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact hk
  · intro he
    have hm : e ∈ N.regionEdges A := by
      apply (N.mem_regionEdges A e).mpr
      by_contra hn
      have ht := (N.capMap_eq_none A (N.tail e)).mpr (not_or.mp hn).1
      have hh := (N.capMap_eq_none A (N.head e)).mpr (not_or.mp hn).2
      rw [ht,hh] at he
      tauto
    exact ⟨⟨e,hm⟩,he,rfl⟩

lemma cap_threeConnected (hN : N.ThreeEdgeConnected) (A : Finset V) (hA : Aᶜ.Nonempty) :
    (N.cap A).ThreeEdgeConnected := by
  intro B hB hBc
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,N.cap_cut]
  apply hN
  · obtain ⟨v,hv⟩ := hB
    obtain ⟨w,rfl⟩ := N.capMap_surjective A hA v
    exact ⟨w,(N.mem_capPreimage A B w).mpr hv⟩
  · obtain ⟨v,hv⟩ := hBc
    obtain ⟨w,rfl⟩ := N.capMap_surjective A hA v
    exact ⟨w,by simpa only [Finset.mem_compl,mem_capPreimage] using hv⟩

lemma threeCut_bond (h : N.ThreeEdgeConnected) (A : Finset V) (hA : (N.cut A).card = 3) : N.Bond A := by
  refine ⟨Finset.card_pos.mp (by omega),?_⟩
  intro B hB
  by_cases hn : (N.cut B).Nonempty
  · right
    obtain ⟨e,he⟩ := hn
    have hc := (N.mem_cut B e).mp he
    have hi : B.Nonempty := hc.elim (fun h => ⟨_,h.1⟩) (fun h => ⟨_,h.1⟩)
    have ho : Bᶜ.Nonempty := hc.elim (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩) (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩)
    exact Finset.eq_of_subset_of_card_le hB (by have hh := h B hi ho; omega)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hn)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma cap_simple (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (A : Finset V) (hcut : (N.cut A).card = 3) (hA : 2 ≤ A.card) (ho : Aᶜ.Nonempty) :
    (N.cap A).Simple := by
  apply (N.cap A).simple_of_cubic_stars (N.cap_loopless hN A)
    (N.cap_star_card hN hc A hcut) (N.cap_threeConnected h3 A ho)
  simp only [Fintype.card_option,Fintype.card_coe]
  omega

lemma cap_cubic (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (A : Finset V) (hcut : (N.cut A).card = 3) (hA : 2 ≤ A.card) (ho : Aᶜ.Nonempty) :
    (N.cap A).graph.IsRegularOfDegree 3 := by
  intro v
  rw [← (N.cap A).card_star (N.cap_simple hN hc h3 A hcut hA ho)]
  exact N.cap_star_card hN hc A hcut v

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network

end OAI

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

lemma cap_duality (h : N.Duality D) (hN : N.Simple) (h3 : N.ThreeEdgeConnected)
    (A : Finset V) (hcut : (N.cut A).card = 3) (ha : A.Nonempty) (ho : Aᶜ.Nonempty) :
    ∃ (L : Type uF) (_ : Fintype L) (dual : Network L (N.regionEdges A)), (N.cap A).Duality dual := by
  have hshore : (N.graph.induce {v | v ∉ A}).Connected := by
    have hh := (N.threeCut_bond h3 A hcut).compl.connected_shore N h.connected ho
      (by obtain ⟨v,hv⟩ := ha; exact ⟨v,by simpa only [Finset.mem_compl,not_not] using hv⟩)
    change (N.graph.induce {v | v ∈ Aᶜ}).Connected at hh
    have heq : {v | v ∈ Aᶜ} = {v | v ∉ A} := by ext v; simp
    rw [heq] at hh
    exact hh
  exact h.minor N D (N.capMap A) (N.capMap_surjective A ho)
    (N.cap_connectedFibers A hshore) Subtype.val Subtype.val_injective
    (N.cap_loopless hN A) ((N.cap_threeConnected h3 A ho).connected (N.cap A))

lemma cap_card_lt (A : Finset V) (ho : 2 ≤ Aᶜ.card) : Fintype.card (Option A) < Fintype.card V := by
  simp only [Fintype.card_option,Fintype.card_coe]
  have hh := Finset.card_add_card_compl A
  omega

end
end Barnette.Network
namespace Barnette.SimpleCycle
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

end
end Barnette.SimpleCycle

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Gluing ----
namespace OAI

/-! Compatible boundary matchings and strong induction over three-edge cuts. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
attribute [local instance] OAI.Barnette.Network.capMatchingEq
omit [Fintype V] in
lemma restrict_star_image (S : Finset E) (v : V) :
    ((N.restrict (Subtype.val : S → E)).star v).image Subtype.val =
      (N.star v).filter (· ∈ S) := by
  ext e
  simp only [Finset.mem_image,Finset.mem_filter,mem_star]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨hk,k.property⟩
  · rintro ⟨he,hs⟩
    exact ⟨⟨e,hs⟩,he,rfl⟩

lemma matching_complement_two (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (P : Finset E) (hP : ∀ v, ((N.star v).filter (· ∈ P)).card = 1) :
    (N.restrict (Subtype.val : ↥Pᶜ → E)).graph.IsRegularOfDegree 2 := by
  intro v
  rw [← card_star _ (hN.restrict N _ Subtype.val_injective),
    ← Finset.card_image_of_injective _ Subtype.val_injective,N.restrict_star_image]
  have he := Finset.card_filter_add_card_filter_not (s := N.star v) (p := fun e => e ∈ P)
  rw [hP v,N.card_star hN,hc v] at he
  simpa only [Finset.mem_compl] using (show ((N.star v).filter (fun e => e ∉ P)).card = 2 by omega)

omit [Fintype V] in
lemma cap_matching_some (A : Finset V) (P : Finset (N.regionEdges A)) (v : A) :
    (((N.cap A).star (some v)).filter (· ∈ P)).image Subtype.val =
      (N.star v.val).filter (· ∈ P.image Subtype.val) := by
  rw [Finset.filter_mem_eq_inter,Finset.image_inter _ _ Subtype.val_injective,
    N.cap_star_some,Finset.filter_mem_eq_inter]

omit [Fintype V] in
lemma cap_matching_none (A : Finset V) (P : Finset (N.regionEdges A)) :
    (((N.cap A).star none).filter (· ∈ P)).image Subtype.val =
      (N.cut A).filter (· ∈ P.image Subtype.val) := by
  rw [Finset.filter_mem_eq_inter,Finset.image_inter _ _ Subtype.val_injective,
    N.cap_star_none,Finset.filter_mem_eq_inter]

omit [Fintype V] in
lemma cap_matching_boundary (A : Finset V) (P : Finset (N.regionEdges A))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1) :
    ∃ c : E, c ∈ N.cut A ∧ c ∈ P.image Subtype.val ∧
      ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e = c := by
  have hh := hP none
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,N.cap_matching_none] at hh
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hh
  have hmem : c ∈ (N.cut A).filter (· ∈ P.image Subtype.val) := by rw [hc]; simp
  refine ⟨c,(Finset.mem_filter.mp hmem).1,(Finset.mem_filter.mp hmem).2,?_⟩
  intro e he
  have heq : e ∈ (N.cut A).filter (· ∈ P.image Subtype.val) ↔ e = c := by rw [hc]; simp
  simpa only [Finset.mem_filter,he,true_and] using heq

omit [Fintype V] in
lemma cap_image_subset (A : Finset V) (P : Finset (N.regionEdges A)) :
    P.image Subtype.val ⊆ N.regionEdges A := by
  rintro e he
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he
  exact k.property

lemma region_pair_inter (A : Finset V) (e : E) :
    e ∈ N.regionEdges A → e ∈ N.regionEdges Aᶜ → e ∈ N.cut A := by
  simp only [mem_regionEdges,mem_cut,Finset.mem_compl]
  tauto

lemma cap_glue_agrees (A : Finset V) (P : Finset (N.regionEdges A))
    (Q : Finset (N.regionEdges Aᶜ))
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val)
    (e : E) (he : e ∈ N.regionEdges A) :
    e ∈ P.image Subtype.val ∪ Q.image Subtype.val ↔ e ∈ P.image Subtype.val := by
  rw [Finset.mem_union,or_iff_left_iff_imp]
  intro hq
  exact (hcut e (N.region_pair_inter A e he (N.cap_image_subset Aᶜ Q hq))).mpr hq

lemma cap_glue_agrees_right (A : Finset V) (P : Finset (N.regionEdges A))
    (Q : Finset (N.regionEdges Aᶜ))
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val)
    (e : E) (he : e ∈ N.regionEdges Aᶜ) :
    e ∈ P.image Subtype.val ∪ Q.image Subtype.val ↔ e ∈ Q.image Subtype.val := by
  rw [Finset.mem_union,or_iff_right_iff_imp]
  intro hp
  exact (hcut e (N.region_pair_inter A e (N.cap_image_subset A P hp) he)).mp hp

lemma cap_glue_matching (A : Finset V) (P : Finset (N.regionEdges A))
    (Q : Finset (N.regionEdges Aᶜ))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1)
    (hQ : ∀ v, (((N.cap Aᶜ).star v).filter (· ∈ Q)).card = 1)
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val) :
    ∀ v, ((N.star v).filter (· ∈ P.image Subtype.val ∪ Q.image Subtype.val)).card = 1 := by
  have side (B : Finset V) (P : Finset (N.regionEdges B)) (R : Finset E)
      (hP : ∀ v, (((N.cap B).star v).filter (· ∈ P)).card = 1)
      (hR : ∀ e ∈ N.regionEdges B, e ∈ R ↔ e ∈ P.image Subtype.val)
      (v : B) : ((N.star v.val).filter (· ∈ R)).card = 1 := by
    have heq : (N.star v.val).filter (· ∈ R) = (N.star v.val).filter (· ∈ P.image Subtype.val) := by
      apply Finset.filter_congr
      intro e he
      apply hR e
      rcases (N.mem_star e v.val).mp he with ht|hh
      · exact (N.mem_regionEdges B e).mpr (Or.inl (ht ▸ v.property))
      · exact (N.mem_regionEdges B e).mpr (Or.inr (hh ▸ v.property))
    rw [heq,← N.cap_matching_some B P v,Finset.card_image_of_injective _ Subtype.val_injective]
    exact hP (some v)
  intro v
  by_cases hv : v ∈ A
  · exact side A P _ hP (N.cap_glue_agrees A P Q hcut) ⟨v,hv⟩
  · exact side Aᶜ Q _ hQ (N.cap_glue_agrees_right A P Q hcut) ⟨v,Finset.mem_compl.mpr hv⟩
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
attribute [local instance] OAI.Barnette.Network.capReachableEq
omit [Fintype V] in
lemma cap_complement_reachable (A : Finset V) (P : Finset (N.regionEdges A))
    (R : Finset E)
    (hc : ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph.Connected)
    (hd : ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph.IsRegularOfDegree 2)
    (hR : ∀ e ∈ N.regionEdges A, e ∈ R ↔ e ∈ P.image Subtype.val)
    (v w : A) : (N.restrict (Subtype.val : ↥Rᶜ → E)).graph.Reachable v.val w.val := by
  let C := ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph
  have hC : (C.induce {x | x ≠ none}).Connected :=
    Barnette.SimpleCycle.delete_vertex_connected C hc hd none
  let f : (C.induce {x | x ≠ none}) →g (N.restrict (Subtype.val : ↥Rᶜ → E)).graph := {
    toFun := fun x => (x.val.getD v).val
    map_rel' := by
      rintro ⟨x,hx⟩ ⟨y,hy⟩ hxy
      cases x with
      | none => exact (hx rfl).elim
      | some x =>
        cases y with
        | none => exact (hy rfl).elim
        | some y =>
          obtain ⟨hne,k,hk⟩ := hxy
          have hxy' : x.val ≠ y.val := by
            intro hh
            have hh' : x = y := Subtype.ext hh
            subst y
            exact hne rfl
          have hk' : (N.tail k.val.val = x.val ∧ N.head k.val.val = y.val) ∨
              (N.tail k.val.val = y.val ∧ N.head k.val.val = x.val) := by
            change (N.capMap A (N.tail k.val.val) = some x ∧ N.capMap A (N.head k.val.val) = some y) ∨
              (N.capMap A (N.tail k.val.val) = some y ∧ N.capMap A (N.head k.val.val) = some x) at hk
            simpa only [capMap_eq_some] using hk
          have hnot : k.val.val ∉ P.image Subtype.val := by
            intro hm
            obtain ⟨e,he,hee⟩ := Finset.mem_image.mp hm
            have hee' : e = k.val := Subtype.ext hee
            exact (Finset.mem_compl.mp k.property) (hee' ▸ he)
          have hkR : k.val.val ∈ Rᶜ :=
            Finset.mem_compl.mpr (hnot ∘ (hR k.val.val k.val.property).mp)
          exact ⟨hxy',⟨k.val.val,hkR⟩,hk'⟩ }
  exact (hC ⟨some v,by simp⟩ ⟨some w,by simp⟩).map f

lemma cap_glue_connected (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (h3 : N.ThreeEdgeConnected) (A : Finset V) (hA : (N.cut A).card = 3)
    (ha : 2 ≤ A.card) (ho : 2 ≤ Aᶜ.card)
    (P : Finset (N.regionEdges A)) (Q : Finset (N.regionEdges Aᶜ))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1)
    (hQ : ∀ v, (((N.cap Aᶜ).star v).filter (· ∈ Q)).card = 1)
    (hPc : ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph.Connected)
    (hQc : ((N.cap Aᶜ).restrict (Subtype.val : ↥Qᶜ → N.regionEdges Aᶜ)).graph.Connected)
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val) :
    (N.restrict (Subtype.val : ↥(P.image Subtype.val ∪ Q.image Subtype.val)ᶜ → E)).graph.Connected := by
  have ha' : A.Nonempty := Finset.card_pos.mp (by omega)
  have ho' : Aᶜ.Nonempty := Finset.card_pos.mp (by omega)
  have hc' : (N.cut Aᶜ).card = 3 := by simpa only [cut_compl] using hA
  have ha'' : (Aᶜ)ᶜ.Nonempty := by simpa only [compl_compl] using ha'
  have hmP := (N.cap A).matching_complement_two (N.cap_simple hN hc h3 A hA ha ho')
    (N.cap_cubic hN hc h3 A hA ha ho') P hP
  have hmQ := (N.cap Aᶜ).matching_complement_two (N.cap_simple hN hc h3 Aᶜ hc' ho ha'')
    (N.cap_cubic hN hc h3 Aᶜ hc' ho ha'') Q hQ
  let R := P.image Subtype.val ∪ Q.image Subtype.val
  let H := (N.restrict (Subtype.val : ↥Rᶜ → E)).graph
  have rA (v w : A) : H.Reachable v.val w.val :=
    N.cap_complement_reachable A P R hPc hmP (N.cap_glue_agrees A P Q hcut) v w
  have rB (v w : ↥(Aᶜ)) : H.Reachable v.val w.val :=
    N.cap_complement_reachable Aᶜ Q R hQc hmQ (N.cap_glue_agrees_right A P Q hcut) v w
  obtain ⟨c,hcA,hcP,hcuniq⟩ := N.cap_matching_boundary A P hP
  have hdex : ((N.cut A).erase c).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hcA,hA]
    decide
  obtain ⟨d,hd⟩ := hdex
  obtain ⟨hdc,hdA⟩ := Finset.mem_erase.mp hd
  have hdP : d ∉ P.image Subtype.val := fun hh => hdc ((hcuniq d hdA).mp hh)
  have hdr : d ∈ N.regionEdges A := by
    have hh := (N.mem_cut A d).mp hdA
    exact (N.mem_regionEdges A d).mpr (hh.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left))
  have hdR : d ∈ Rᶜ := Finset.mem_compl.mpr
    (hdP ∘ (N.cap_glue_agrees A P Q hcut d hdr).mp)
  have adj : H.Adj (N.tail d) (N.head d) := ⟨hN.loopless d,⟨d,hdR⟩,Or.inl ⟨rfl,rfl⟩⟩
  have cross (x y : V) (hx : x ∈ A) (hy : y ∉ A) (hxy : H.Adj x y) : H.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
    refine ⟨x,?_⟩
    intro z
    by_cases hz : z ∈ A
    · exact rA ⟨x,hx⟩ ⟨z,hz⟩
    · exact hxy.reachable.trans (rB ⟨y,Finset.mem_compl.mpr hy⟩ ⟨z,Finset.mem_compl.mpr hz⟩)
  rcases (N.mem_cut A d).mp hdA with ⟨ht,hh⟩|⟨hh,ht⟩
  · exact cross _ _ ht hh adj
  · exact cross _ _ hh ht adj.symm
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
universe uV uE uF
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] (N : Network V E)
attribute [local instance] OAI.Barnette.Network.unrestrictedInductionEq
omit [Fintype V] in
lemma cap_matching_boundary_at (A : Finset V) (P : Finset (N.regionEdges A))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1)
    (c : E) (hc : c ∈ N.cut A) (hm : c ∈ P.image Subtype.val) :
    ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e = c := by
  obtain ⟨d,_,_,hd⟩ := N.cap_matching_boundary A P hP
  have hh : c = d := (hd c hc).mp hm
  subst d
  exact hd

lemma nontrivial_threeCut_at (h : ¬N.TrivialThreeCuts) (e : E) :
    ∃ A : Finset V, (N.cut A).card = 3 ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card ∧ e ∈ N.regionEdges A := by
  obtain ⟨A,hA,ha,ho⟩ := N.nontrivial_threeCut h
  by_cases he : e ∈ N.regionEdges A
  · exact ⟨A,hA,ha,ho,he⟩
  · have ht : N.tail e ∉ A := fun hh => he ((N.mem_regionEdges A e).mpr (Or.inl hh))
    refine ⟨Aᶜ,by simpa only [cut_compl] using hA,ho,by simpa only [compl_compl] using ha,?_⟩
    exact (N.mem_regionEdges Aᶜ e).mpr (Or.inl (Finset.mem_compl.mpr ht))

private theorem matching_strong (n : ℕ) :
    ∀ {V : Type uV} {E : Type uE} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
      (N : Network V E) (D : Network F E), Fintype.card V = n →
      N.Duality D → N.Simple → N.graph.IsRegularOfDegree 3 → N.ThreeEdgeConnected →
      ∀ (black : V → Prop), (∀ e, black (N.tail e) ↔ ¬black (N.head e)) →
      ∀ e : E, ∃ P : Finset E, e ∈ P ∧ (∀ v, ((N.star v).filter (· ∈ P)).card = 1) ∧
        (N.restrict (Subtype.val : ↥Pᶜ → E)).graph.Connected := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E F _ _ _ N D hn h hN hc h3 black hb e
    by_cases ht : N.TrivialThreeCuts
    · obtain ⟨M⟩ := N.make_coloredDual D h hN h3 hc black hb
      exact N.irreducible_matching D M h3 ht e
    · obtain ⟨A,hA,ha,ho,he⟩ := N.nontrivial_threeCut_at ht e
      have ha' : A.Nonempty := Finset.card_pos.mp (by omega)
      have ho' : Aᶜ.Nonempty := Finset.card_pos.mp (by omega)
      have hc' : (N.cut Aᶜ).card = 3 := by simpa only [cut_compl] using hA
      have ha'' : (Aᶜ)ᶜ.Nonempty := by simpa only [compl_compl] using ha'
      obtain ⟨F₁,f₁,D₁,h₁⟩ := N.cap_duality D h hN h3 A hA ha' ho'
      let : Fintype F₁ := f₁
      have hlt₁ : Fintype.card (Option A) < n := hn ▸ cap_card_lt A ho
      obtain ⟨P,heP,hP,hPc⟩ := ih _ hlt₁ (N.cap A) D₁ rfl h₁
        (N.cap_simple hN hc h3 A hA ha ho') (N.cap_cubic hN hc h3 A hA ha ho')
        (N.cap_threeConnected h3 A ho') (N.capBlack black A)
        (N.cap_coloring hN hc black hb A hA) ⟨e,he⟩
      obtain ⟨c,hca,hcp,hcu⟩ := N.cap_matching_boundary A P hP
      have hcb : c ∈ N.cut Aᶜ := by simpa only [cut_compl] using hca
      have hcr : c ∈ N.regionEdges Aᶜ := by
        have hh := (N.mem_cut Aᶜ c).mp hcb
        exact (N.mem_regionEdges Aᶜ c).mpr (hh.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left))
      obtain ⟨F₂,f₂,D₂,h₂⟩ := N.cap_duality D h hN h3 Aᶜ hc' ho' ha''
      let : Fintype F₂ := f₂
      have hlt₂ : Fintype.card (Option ↥(Aᶜ)) < n := by
        rw [← hn]
        exact cap_card_lt Aᶜ (by simpa only [compl_compl] using ha)
      obtain ⟨Q,hcQ,hQ,hQc⟩ := ih _ hlt₂ (N.cap Aᶜ) D₂ rfl h₂
        (N.cap_simple hN hc h3 Aᶜ hc' ho ha'') (N.cap_cubic hN hc h3 Aᶜ hc' ho ha'')
        (N.cap_threeConnected h3 Aᶜ ha'') (N.capBlack black Aᶜ)
        (N.cap_coloring hN hc black hb Aᶜ hc') ⟨c,hcr⟩
      have hcQ' : c ∈ Q.image Subtype.val := Finset.mem_image.mpr ⟨⟨c,hcr⟩,hcQ,rfl⟩
      have hqcut : ∀ d ∈ N.cut A, d ∈ Q.image Subtype.val ↔ d = c := by
        simpa only [cut_compl] using N.cap_matching_boundary_at Aᶜ Q hQ c hcb hcQ'
      have hcut : ∀ d ∈ N.cut A, d ∈ P.image Subtype.val ↔ d ∈ Q.image Subtype.val :=
        fun d hd => (hcu d hd).trans (hqcut d hd).symm
      refine ⟨P.image Subtype.val ∪ Q.image Subtype.val,?_,N.cap_glue_matching A P Q hP hQ hcut,?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨e,he⟩,heP,rfl⟩)
      · exact N.cap_glue_connected hN hc h3 A hA ha ho P Q hP hQ hPc hQc hcut

variable {F : Type uF} [Fintype F] (D : Network F E)

theorem Duality.connected_complement_matching (h : N.Duality D) (hN : N.Simple)
    (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    ∃ P : Finset E, e ∈ P ∧ (∀ v, ((N.star v).filter (· ∈ P)).card = 1) ∧
      (N.restrict (Subtype.val : ↥Pᶜ → E)).graph.Connected :=
  matching_strong (Fintype.card V) N D rfl h hN hc h3 black hb e
end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.MinorModel ----
namespace OAI

/-! Clean finite walks, disjoint grown branches, and lattice minors. -/

namespace Barnette

noncomputable section

namespace WalkSelection

variable {W : Type*} {H : SimpleGraph W}

namespace CleanConnection
variable {A B C : Set W} (p : CleanConnection (H := H) A B C)

end CleanConnection

end WalkSelection
end
end Barnette

namespace Barnette

namespace CorridorModel
noncomputable section
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

variable (M : CorridorModel G H)

variable [Fintype V]

end
end CorridorModel
end Barnette

namespace Barnette.PlaneEmbedding
noncomputable section
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_lattice_minor_model (E : PlaneEmbedding G) :
    Nonempty (MinorModel G SquareGrid.graph) := by
  classical
  obtain ⟨M⟩ := E.exists_lattice_corridor_model
  exact ⟨M.toMinorModel⟩
end
end Barnette.PlaneEmbedding

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Rectangle ----
namespace OAI

/-! Rectangular primal and dual networks and finite lattice containment. -/

namespace Barnette.RectangularDual
noncomputable section

lemma sum_succ {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (∑ i, if i.succ = v then f i else 0) = lowerValue f v := by
  induction v using Fin.cases with
  | zero => simp [lowerValue]
  | succ v => simp [lowerValue]

lemma sum_castSucc {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (∑ i, if i.castSucc = v then f i else 0) = upperValue f v := by
  induction v using Fin.lastCases with
  | last => simp [upperValue, Fin.castSucc_ne_last]
  | cast v => simp [upperValue]

lemma sum_stepCoeff {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (∑ i, stepCoeff v i * f i) = lowerValue f v - upperValue f v := by
  simp only [stepCoeff, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, sum_succ, sum_castSucc]

lemma lower_eval {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (lower v).elim 0 f = lowerValue f v := by
  induction v using Fin.cases <;> simp [lower, lowerValue]

lemma upper_eval {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (upper v).elim 0 f = upperValue f v := by
  induction v using Fin.lastCases <;> simp [upper, upperValue]

lemma eval_map {A B : Type*} (g : B → ℝ) (f : A → B) (z : Option A) :
    (z.map f).elim 0 g = z.elim 0 (g ∘ f) := by cases z <;> rfl

lemma dual_horizontal {n m : ℕ} (f : Fin n × Fin m → ℝ)
    (i : Fin n) (j : Fin (m + 1)) :
    (dual n m).gradient (potential f) (.inl (i, j)) =
      -∑ q, stepCoeff j q * f (i, q) := by
  change ((upper j).map _).elim 0 f - ((lower j).map _).elim 0 f = _
  rw [eval_map, eval_map, upper_eval, lower_eval, sum_stepCoeff]
  dsimp only [Function.comp_def]
  ring

lemma dual_vertical {n m : ℕ} (f : Fin n × Fin m → ℝ)
    (i : Fin (n + 1)) (j : Fin m) :
    (dual n m).gradient (potential f) (.inr (i, j)) =
      ∑ p, stepCoeff i p * f (p, j) := by
  change ((lower i).map _).elim 0 f - ((upper i).map _).elim 0 f = _
  rw [eval_map, eval_map, upper_eval, lower_eval, sum_stepCoeff]
  rfl

lemma boundary_formula {n m : ℕ} (x : Edge n m → ℝ) (i : Fin (n + 1))
    (j : Fin (m + 1)) :
    (primal n m).boundary x (i, j) =
      (∑ p, stepCoeff i p * x (.inl (p, j))) +
      (∑ q, stepCoeff j q * x (.inr (i, q))) := by
  classical
  rw [Network.boundary_apply, Fintype.sum_sum_type]
  simp only [primal, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq,
    Fintype.sum_prod_type, stepCoeff, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, ite_and]
  simp

lemma orthogonal_potential (n m : ℕ) (f : Fin n × Fin m → ℝ) :
    (primal n m).boundary ((dual n m).gradient (potential f)) = 0 := by
  ext ⟨i, j⟩
  rw [boundary_formula]
  simp only [dual_horizontal, dual_vertical, mul_neg, Finset.sum_neg_distrib,
    Finset.mul_sum]
  rw [Finset.sum_comm (f := fun q p => stepCoeff j q * (stepCoeff i p * f (p, q)))]
  have he : (∑ p, ∑ q, stepCoeff j q * (stepCoeff i p * f (p, q))) =
      ∑ p, ∑ q, stepCoeff i p * (stepCoeff j q * f (p, q)) := by
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he]
  exact neg_add_cancel _

lemma orthogonal (n m : ℕ) (f : Face n m → ℝ) :
    (primal n m).boundary ((dual n m).gradient f) = 0 := by
  let g : Fin n × Fin m → ℝ := fun t => f (some t) - f none
  have hf : f = potential g + (fun _ => f none) := by
    ext z
    cases z <;> simp [potential, g]
  rw [hf, map_add, Network.gradient_const, add_zero]
  exact orthogonal_potential n m g

lemma horizontal_adj {n m : ℕ} (i : Fin n) (j : Fin (m + 1)) :
    (primal n m).graph.Adj (i.castSucc, j) (i.succ, j) := by
  refine ⟨?_, .inl (i, j), Or.inl ⟨rfl, rfl⟩⟩
  intro h
  have hh := congrArg (fun z : Vertex n m => z.1.val) h
  simp only [Fin.val_castSucc, Fin.val_succ] at hh
  omega

lemma vertical_adj {n m : ℕ} (i : Fin (n + 1)) (j : Fin m) :
    (primal n m).graph.Adj (i, j.castSucc) (i, j.succ) := by
  refine ⟨?_, .inr (i, j), Or.inl ⟨rfl, rfl⟩⟩
  intro h
  have hh := congrArg (fun z : Vertex n m => z.2.val) h
  simp only [Fin.val_castSucc, Fin.val_succ] at hh
  omega

lemma primal_connected (n m : ℕ) : (primal n m).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨(0, 0), ?_⟩
  rintro ⟨i, j⟩
  have hv : (primal n m).graph.Reachable (0, 0) (0, j) := by
    induction j using Fin.induction with
    | zero => exact .rfl
    | succ j ih => exact ih.trans (vertical_adj (0 : Fin (n + 1)) j).reachable
  have hh : (primal n m).graph.Reachable (0, j) (i, j) := by
    induction i using Fin.induction with
    | zero => exact .rfl
    | succ i ih => exact ih.trans (horizontal_adj i j).reachable
  exact hv.trans hh

lemma dual_connected (n m : ℕ) : (dual n m).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none, ?_⟩
  intro z
  cases z with
  | none => exact .rfl
  | some z =>
    obtain ⟨i, j⟩ := z
    cases n with
    | zero => exact isEmptyElim i
    | succ n =>
      induction i using Fin.induction with
      | zero =>
        have h := ((dual (n + 1) m).edge_reachable (.inr (0, j))).symm
        have hu : upper (0 : Fin (n + 2)) = some (0 : Fin (n + 1)) := by
          change upper (0 : Fin (n + 1)).castSucc = _
          exact Fin.lastCases_castSucc _
        simpa only [dual, Sum.elim_inr, lower, Fin.cases_zero, hu,
          Option.map_none, Option.map_some] using h
      | succ i ih =>
        have h := ((dual (n + 1) m).edge_reachable (.inr (i.succ.castSucc, j))).symm
        have hl : lower i.succ.castSucc = some i.castSucc := by
          have he : i.succ.castSucc = i.castSucc.succ := by ext; rfl
          rw [he]
          simp [lower]
        have hu : upper i.succ.castSucc = some i.succ := Fin.lastCases_castSucc _
        exact ih.trans (by
          simpa only [dual, Sum.elim_inr, hl, hu, Option.map_some] using h)

theorem grid_duality (n m : ℕ) : (primal n m).Duality (dual n m) := by
  apply Network.duality_of_orth_card (primal n m) (dual n m)
    (primal_connected n m) (dual_connected n m)
  · simp only [Vertex, Face, Edge, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_option, Fintype.card_sum]
    ring
  · exact orthogonal n m

end
end Barnette.RectangularDual

namespace Barnette.MinorModel
noncomputable section
open scoped Classical
variable {V W U : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  {J : SimpleGraph U} [Fintype U]

end
end Barnette.MinorModel

namespace Barnette.RectangularDual
noncomputable section
open scoped Classical

lemma bounded_mem_range (r : ℕ) (z : ℤ × ℤ)
    (h₁ : z.1.natAbs ≤ r) (h₂ : z.2.natAbs ≤ r) :
    z ∈ Set.range (latticeEmbedding r) := by
  have ha : z.1 ≤ (z.1.natAbs : ℤ) := Int.le_natAbs
  have hb : -z.1 ≤ (z.1.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -z.1))
  have hc : z.2 ≤ (z.2.natAbs : ℤ) := Int.le_natAbs
  have hd : -z.2 ≤ (z.2.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -z.2))
  refine ⟨(⟨(z.1 + r).toNat, ?_⟩, ⟨(z.2 + r).toNat, ?_⟩), ?_⟩
  · omega
  · omega
  · apply Prod.ext <;> dsimp [latticeEmbedding, latticePoint] <;> omega

lemma finite_subset_box (s : Set (ℤ × ℤ)) (hs : s.Finite) :
    ∃ r : ℕ, s ⊆ Set.range (latticeEmbedding r) := by
  let r := ∑ z ∈ hs.toFinset, (z.1.natAbs + z.2.natAbs)
  refine ⟨r, ?_⟩
  intro z hz
  have hle : z.1.natAbs + z.2.natAbs ≤ r :=
    Finset.single_le_sum (f := fun z : ℤ × ℤ => z.1.natAbs + z.2.natAbs)
      (fun _ _ => Nat.zero_le _) (hs.mem_toFinset.mpr hz)
  exact bounded_mem_range r z (by omega) (by omega)

theorem lattice_minor_in_rectangle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : MinorModel G SquareGrid.graph) :
    ∃ r : ℕ, Nonempty (MinorModel G (primal (2 * r) (2 * r)).graph) := by
  let s := ⋃ v, M.branch v
  have hs : s.Finite := Set.finite_iUnion M.branch_finite
  obtain ⟨r, hr⟩ := finite_subset_box s hs
  refine ⟨r, ⟨M.pullHost (latticeEmbedding r) ?_⟩⟩
  intro v z hz
  exact hr (Set.mem_iUnion.mpr ⟨v, hz⟩)

end
end Barnette.RectangularDual

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.ExactDual ----
namespace OAI

/-! Graph realization and exact finite duality for topological plane embeddings. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V W E : Type*} [Fintype V] [Fintype W] [Fintype E]

omit [Fintype V] in
lemma Realizes.graph_eq {G : SimpleGraph V} {M : Network V G.edgeSet}
    (h : M.Realizes G) : M.graph = G := by
  ext v w
  constructor
  · rintro ⟨_, e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact G.mem_edgeSet.mp ((h e).symm ▸ e.property)
    · exact (G.mem_edgeSet.mp ((h e).symm ▸ e.property)).symm
  · intro hvw
    let e : G.edgeSet := ⟨s(v,w), hvw⟩
    refine ⟨hvw.ne, e, ?_⟩
    have he := h e
    change s(M.tail e, M.head e) = s(v,w) at he
    exact Sym2.eq_iff.mp he

omit [Fintype V] in
lemma Realizes.loopless {G : SimpleGraph V} {M : Network V G.edgeSet}
    (h : M.Realizes G) (e : G.edgeSet) : M.tail e ≠ M.head e := by
  have he : G.Adj (M.tail e) (M.head e) := G.mem_edgeSet.mp ((h e).symm ▸ e.property)
  exact he.ne

omit [Fintype V] in
lemma exists_dart_for_edge (G : SimpleGraph V) (e : G.edgeSet) :
    ∃ d : G.Dart, d.edge = e.val := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf x y => exact ⟨⟨(x,y), he⟩, rfl⟩

omit [Fintype V] [Fintype W] [Fintype E] in
lemma connectedFibers_of_partition (N : Network W E) (q : W → V)
    (B : V → Set W) (hB : ∀ v, (N.graph.induce (B v)).Connected)
    (hmem : ∀ w v, q w = v ↔ w ∈ B v) : N.ConnectedFibers q := by
  intro x y hxy
  let T := N.restrict (Subtype.val : N.internal q → E)
  let f : N.graph.induce (B (q x)) →g T.graph := {
    toFun := Subtype.val
    map_rel' := by
      intro a b hab
      rcases hab with ⟨hne, e, he⟩
      have ha : q a.val = q x := (hmem _ _).mpr a.property
      have hb : q b.val = q x := (hmem _ _).mpr b.property
      have hei : e ∈ N.internal q := by
        rcases he with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · change q (N.tail e) = q (N.head e)
          rw [ht, hh]; exact ha.trans hb.symm
        · change q (N.tail e) = q (N.head e)
          rw [ht, hh]; exact hb.trans ha.symm
      exact ⟨hne, ⟨e, hei⟩, he⟩ }
  have hx : x ∈ B (q x) := (hmem x (q x)).mp rfl
  have hy : y ∈ B (q x) := (hmem y (q x)).mp hxy.symm
  exact ((hB (q x)) ⟨x,hx⟩ ⟨y,hy⟩).map f

omit [Fintype E] in

theorem minor_quotient {G : SimpleGraph V} (hG : G.Connected)
    (N : Network W E) (hN : N.graph.Connected) (M : MinorModel G N.graph) :
    ∃ (q : W → V) (j : G.edgeSet → E), Function.Surjective q ∧
      N.ConnectedFibers q ∧ Function.Injective j ∧
      ((N.mapVertices q).restrict j).Realizes G := by
  have : Nonempty V := hG.nonempty
  obtain ⟨B, hsub, hconn, hdisj, hcover⟩ := BranchPartition.extend N.graph hN
    M.branch M.branch_connected M.branches_disjoint
  obtain ⟨q, hq, hmem⟩ := BranchPartition.quotient N.graph B hconn hdisj hcover
  choose d hd using exists_dart_for_edge G
  have hex (e : G.edgeSet) : ∃ k : E, s(q (N.tail k), q (N.head k)) = e.val := by
    obtain ⟨a, ha, b, hb, _, k, hk⟩ := M.adjacency (d e).fst (d e).snd (d e).adj
    have ha' : q a = (d e).fst := (hmem _ _).mpr (hsub _ ha)
    have hb' : q b = (d e).snd := (hmem _ _).mpr (hsub _ hb)
    refine ⟨k, ?_⟩
    rcases hk with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · rw [ht, hh, ha', hb']; exact hd e
    · rw [ht, hh, ha', hb', Sym2.eq_swap]; exact hd e
  choose j hj using hex
  refine ⟨q, j, hq, N.connectedFibers_of_partition q B hconn hmem, ?_, hj⟩
  intro e f hef
  apply Subtype.ext
  exact (hj e).symm.trans ((congrArg (fun k => s(q (N.tail k), q (N.head k))) hef).trans (hj f))

universe uF
variable {F : Type uF} [Fintype F]

theorem Duality.graphMinor {G : SimpleGraph V} (hG : G.Connected)
    (N : Network W E) (D : Network F E) (h : N.Duality D)
    (M : MinorModel G N.graph) :
    ∃ (P : Network V G.edgeSet) (L : Type uF) (_ : Fintype L) (Q : Network L G.edgeSet),
      P.Realizes G ∧ P.Duality Q := by
  obtain ⟨q,j,hq,hc,hj,hreal⟩ := minor_quotient hG N h.connected M
  have he (e : G.edgeSet) : q (N.tail (j e)) ≠ q (N.head (j e)) := hreal.loopless e
  have hPc : ((N.mapVertices q).restrict j).graph.Connected := by
    rw [hreal.graph_eq]; exact hG
  obtain ⟨L, hL, Q, hQ⟩ := h.minor N D q hq hc j hj he hPc
  exact ⟨_, L, hL, Q, hreal, hQ⟩

end
end Barnette.Network

namespace Barnette.PlaneEmbedding
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_exact_dual (E : PlaneEmbedding G) (hG : G.Connected) :
    ∃ (P : Network V G.edgeSet) (F : Type) (_ : Fintype F) (D : Network F G.edgeSet),
      P.Realizes G ∧ P.Duality D := by
  obtain ⟨M⟩ := E.exists_lattice_minor_model
  obtain ⟨r, ⟨M'⟩⟩ := RectangularDual.lattice_minor_in_rectangle M
  exact (RectangularDual.grid_duality (2*r) (2*r)).graphMinor hG _ _ M'
end
end Barnette.PlaneEmbedding

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Main ----
namespace OAI

/-! Hamiltonian cycles in cubic bipartite three-vertex-connected plane graphs. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] (N : Network V E) (D : Network F E)

theorem Duality.hamiltonian (h : N.Duality D) (hN : N.Simple)
    (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    HasHamiltonianCycle N.graph := by
  obtain ⟨v⟩ := h.connected.nonempty
  have hs : (N.star v).Nonempty := by
    apply Finset.card_pos.mp
    rw [N.card_star hN,hc v]
    decide
  obtain ⟨e,_⟩ := hs
  obtain ⟨P,_,hP,hPc⟩ := h.connected_complement_matching N D hN hc h3 black hb e
  let H := (N.restrict (Subtype.val : ↥Pᶜ → E)).graph
  have hdeg : H.IsRegularOfDegree 2 := N.matching_complement_two hN hc P hP
  obtain ⟨p,hp⟩ := Barnette.SimpleCycle.cycle_at_of_connected_two H hPc hdeg v
  let f : H →g N.graph := {
    toFun := id
    map_rel' := by
      rintro a b ⟨hne,k,hk⟩
      exact ⟨hne,k.val,hk⟩ }
  exact ⟨v,p.map f,hp.map Function.bijective_id⟩
end
end Barnette.Network

namespace Barnette
universe u
noncomputable section
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

lemma ThreeVertexConnected.connected (h : ThreeVertexConnected G) : G.Connected := by
  let H := G.induce {v | v ∉ (∅ : Finset V)}
  let f : H →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  exact (h.2 ∅ (by simp)).map f (fun v => ⟨⟨v,by simp⟩,rfl⟩)

theorem main : MainStatement.{u} := by
  intro V hV dV G dG hc hb hp h3
  have hdeq : dV = Classical.decEq V := Subsingleton.elim _ _
  subst dV
  have hdrel : dG = fun a b => Classical.propDecidable (G.Adj a b) := Subsingleton.elim _ _
  subst dG
  obtain ⟨E⟩ := hp
  have hconn := h3.connected
  let : Nonempty V := hconn.nonempty
  have horder := cubic_bipartite_order hc hb
  obtain ⟨N,F,f,D,hr,hd⟩ := E.exists_exact_dual hconn
  let : Fintype F := f
  have hN : N.Simple := by
    refine ⟨hr.loopless,?_⟩
    intro e f hef
    apply Subtype.ext
    rw [← hr e,← hr f]
    exact hef
  have hc' : N.graph.IsRegularOfDegree 3 := by rw [hr.graph_eq]; exact hc
  have h3' : ThreeVertexConnected N.graph := hr.graph_eq.symm ▸ h3
  have hec : N.ThreeEdgeConnected := by
    intro A ha ho
    obtain ⟨w,hw⟩ := ho
    exact N.cut_card_three h3' (by omega) A ha ⟨w,Finset.mem_compl.mp hw⟩
  obtain ⟨color⟩ := hb
  let black : V → Prop := fun v => color v = 0
  have hcolor (e : G.edgeSet) : black (N.tail e) ↔ ¬black (N.head e) := by
    have hne := color.valid (G.mem_edgeSet.mp ((hr e).symm ▸ e.property))
    have ht := (color (N.tail e)).isLt
    have hh := (color (N.head e)).isLt
    have hne' : (color (N.tail e)).val ≠ (color (N.head e)).val := fun h => hne (Fin.ext h)
    change color (N.tail e) = 0 ↔ ¬color (N.head e) = 0
    simp only [Fin.ext_iff,Fin.val_zero]
    omega
  have hh := hd.hamiltonian N D hN hc' hec black hcolor
  rwa [hr.graph_eq] at hh
end
end Barnette

end OAI

-- ---- mission target ----
open OAI OAI.Barnette
universe u
open scoped Classical

namespace OAI
namespace Barnette
theorem _root_.solution : MainStatement.{u} := by
  first
    | exact OAI.Barnette.main
    | (apply OAI.Barnette.main <;> assumption)
    | (intros; apply OAI.Barnette.main <;> assumption)
end Barnette
end OAI
