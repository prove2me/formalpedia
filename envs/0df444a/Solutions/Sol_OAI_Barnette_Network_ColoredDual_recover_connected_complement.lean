-- Prove2me | solution 1 for OAI.Barnette.Network.ColoredDual.recover_connected_complement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:40:13.963967+00:00
-- url     : https://prove2.me/submissions/98693a41-90f6-48a5-879c-e122efde363f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ForestMatching.lean:L379-L395
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.ColoredDual.recover_connected_complement. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_ColoredDual_remainder_black_degree
import Theorems.Thm_OAI_Barnette_Network_ColoredDual_removed_at_black
import Theorems.Thm_OAI_Barnette_Network_addSink_acyclic
import Theorems.Thm_OAI_Barnette_Network_black_dual_card
import Theorems.Thm_OAI_Barnette_Network_black_edge_partition
import Theorems.Thm_OAI_Barnette_Network_card_star
import Theorems.Thm_OAI_Barnette_Network_connected_of_kernel_constants
import Theorems.Thm_OAI_Barnette_Network_cubic_black_region_count
import Theorems.Thm_OAI_Barnette_Network_cubic_region_count
import Theorems.Thm_OAI_Barnette_Network_state_disk_delta
import Theorems.Thm_OAI_Barnette_Network_tree_matching
import Theorems.Thm_OAI_Barnette_TriangleSystem_oppositeGraph_adj_iff
import Theorems.Thm_OAI_Barnette_cycleCoordinates_of_not_acyclic

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

theorem Duality.euler (h : N.Duality D) :
    Fintype.card V + Fintype.card F = Fintype.card E + 2 := by
  have h₁ := N.dim_cycles h.connected
  rw [h.cycles_eq_cuts] at h₁
  have h₂ := D.rank_gradient h.dual_connected
  omega

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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Minimal flow circuits, triangular faces, and simple cycle coordinates. -/

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

omit [Fintype V] [Fintype E] in
lemma otherEnd_spec (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    v ≠ N.otherEnd e v ∧ s(N.tail e,N.head e) = s(v,N.otherEnd e v) := by
  rcases hi with ht | hh
  · rw [otherEnd,ite_eq_left ht]
    exact ⟨ht ▸ h.loopless e, by rw [ht]⟩
  · by_cases ht : N.tail e = v
    · exact (h.loopless e (ht.trans hh.symm)).elim
    · rw [otherEnd,ite_eq_right ht]
      exact ⟨hh ▸ (h.loopless e).symm, by rw [hh,Sym2.eq_swap]⟩

end
end Barnette.Network
namespace Barnette

open Fin.NatCast

theorem cyclic_two_ne_zero (n : ℕ) : (2 : Fin (n + 3)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at this

namespace CycleCoordinates

variable {V : Type*} {G : SimpleGraph V} (C : CycleCoordinates G)

theorem edge_indices_unique (i j : Fin (C.n + 3))
    (h : (C.vertex i = C.vertex j ∧ C.vertex (i + 1) = C.vertex (j + 1)) ∨
      (C.vertex i = C.vertex (j + 1) ∧ C.vertex (i + 1) = C.vertex j)) : i = j := by
  rcases h with h | h
  · exact C.vertex.injective h.1
  · have hi := C.vertex.injective h.1
    have hj := C.vertex.injective h.2
    have hh : (2 : Fin (C.n + 3)) = 0 := by
      have : j + (1 + 1) = j + 0 := by simpa [hi, add_assoc] using hj
      simpa only [show (1 : Fin (C.n + 3)) + 1 = 2 by
        apply Fin.ext
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < C.n + 3 by omega)]] using (add_left_cancel this)
    exact (cyclic_two_ne_zero C.n hh).elim

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
lemma cycleEdge_injective : Function.Injective (N.cycleEdge C) := by
  intro i j hij
  apply C.edge_indices_unique i j
  apply Sym2.eq_iff.mp
  rw [← N.cycleEdge_ends C i, ← N.cycleEdge_ends C j, hij]

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
lemma push_subtype_apply (A : Finset V) (f : A → ℝ) (v : A) :
    push (Subtype.val : A → V) f v.val = f v := by
  have h := congrFun (pull_push_injective (E := V) Subtype.val_injective f) v
  exact h

omit [Fintype V] in
lemma push_subtype_outside (A : Finset V) (f : A → ℝ) {v : V} (hv : v ∉ A) :
    push (Subtype.val : A → V) f v = 0 :=
  push_eq_zero_outside f (by simpa using hv)

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

-- ---- from OAI.Combinatorics.Hamiltonian.ColoredDual ----
namespace OAI

/-! Colored dual networks and signed directed state cycles. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

namespace ColoredDual
variable {N D} (M : N.ColoredDual D)

omit [Fintype F] in
lemma assignment_inj {root : V} (s : M.State root) :
    Set.InjOn (M.assignment s) {v | M.black v ∧ v ≠ root} := by
  intro v hv w hw h
  have hh : s.value ⟨v,hv⟩ = s.value ⟨w,hw⟩ :=
    (M.assignment_apply s ⟨v,hv⟩).symm.trans (h.trans (M.assignment_apply s ⟨w,hw⟩))
  exact congrArg Subtype.val (s.value_injective hh)

omit [Fintype F] in
lemma assignment_face {root : V} (s : M.State root) (v : V)
    (hv : M.black v) (hr : v ≠ root) :
    M.assignment s v ∈ Set.range (M.face v).corner := by
  rw [M.assignment_apply s ⟨v,hv,hr⟩]
  exact ⟨s.val ⟨v,hv,hr⟩,rfl⟩

omit [Fintype F] in
lemma assignment_range {root : V} (s : M.State root) (z : F) :
    z ∉ Set.range (M.face root).corner ↔
      ∃ v, M.black v ∧ v ≠ root ∧ M.assignment s v = z := by
  constructor
  · intro hz
    have hm : z ∈ M.nonroots root := hz
    obtain ⟨t,ht⟩ := (Set.ext_iff.mp s.value_range z).mpr hm
    exact ⟨t.val,t.property.1,t.property.2,(M.assignment_apply s t).trans ht⟩
  · rintro ⟨v,hv,hr,rfl⟩
    rw [M.assignment_apply s ⟨v,hv,hr⟩]
    exact s.value_mem ⟨v,hv,hr⟩

lemma cycle_disk {root : V} (s : M.State root)
    (C : Barnette.CycleCoordinates D.graph)
    (t : Fin (C.n+3) → M.Black root)
    (he : ∀ i, D.cycleEdge C i ∈ N.star (t i).val)
    (hv : ∀ i, s.value (t i) = C.vertex i) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ (c = 1 ∨ c = -1) ∧
      D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.cycleEdges C ∧
      (N.cut A).card = 2 * (N.blackCut M.black A).card + 3 ∧
      N.blackDelta D M.black C = -3*c := by
  apply N.state_disk_delta D M.duality M.simple M.cubic M.dual_simple M.face
    M.black M.coloring root (M.assignment s) (M.assignment_inj s)
    (M.assignment_face s) (M.assignment_range s) C
  intro i
  have hb := N.blackEndpoint_eq M.black M.coloring (t i).property.1
    ((N.mem_star _ _).mp (he i))
  rw [hb]
  exact ⟨(t i).property.2,(M.assignment_apply s (t i)).trans (hv i)⟩

end ColoredDual
end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

namespace StateCycle
variable {M} {root : V} {s : M.State root} (C : M.StateCycle s)

end StateCycle
end
end Barnette.Network.ColoredDual

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.Matching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-! Disk and spoke signs and matching complements. -/

namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma acyclic_conserved_zero (hN : N.Simple) (ha : N.graph.IsAcyclic)
    (x : E → ℝ) (hx : N.boundary x = 0) : x = 0 := by
  ext e
  let K := N.graph.deleteEdges {s(N.tail e,N.head e)}
  have he : N.graph.Adj (N.tail e) (N.head e) := ⟨hN.loopless e,e,Or.inl ⟨rfl,rfl⟩⟩
  have hb : ¬K.Reachable (N.tail e) (N.head e) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ha he)
  let f : V → ℝ := fun v => if K.Reachable (N.tail e) v then 1 else 0
  have hg : N.gradient f e = -1 := by simp [gradient_apply,f,hb]
  have hk : ∀ k, k ≠ e → N.gradient f k = 0 := by
    intro k hke
    have hp : s(N.tail k,N.head k) ≠ s(N.tail e,N.head e) :=
      fun h => hke (hN.pair_injective h)
    have hadj : K.Adj (N.tail k) (N.head k) := by
      apply SimpleGraph.deleteEdges_adj.mpr
      exact ⟨⟨hN.loopless k,k,Or.inl ⟨rfl,rfl⟩⟩,by simpa only [Set.mem_singleton_iff] using hp⟩
    have hh : K.Reachable (N.tail e) (N.head k) ↔ K.Reachable (N.tail e) (N.tail k) :=
      ⟨fun h => h.trans hadj.reachable.symm,fun h => h.trans hadj.reachable⟩
    simp [gradient_apply,f,hh]
  have hi := N.boundary_adjoint x f
  rw [hx] at hi
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero] at hi
  rw [Finset.sum_eq_single e] at hi
  · simpa [hg] using hi.symm
  · intro k _ hke; rw [hk k hke,mul_zero]
  · simp

omit [Fintype V] [Fintype E] in
lemma Simple.restrict (hN : N.Simple) {K : Type*} (j : K → E) (hj : Function.Injective j) :
    (N.restrict j).Simple where
  loopless k := hN.loopless (j k)
  pair_injective _ _ h := hj (hN.pair_injective h)

omit [Fintype E] in
lemma extend_restriction (S : Finset E) (x : E → ℝ) (hx : ∀ e, e ∉ S → x e = 0) :
    push (Subtype.val : S → E) (fun e => x e.val) = x := by
  ext e
  by_cases he : e ∈ S
  · exact push_subtype_apply S (fun e => x e.val) ⟨e,he⟩
  · rw [push_subtype_outside S _ he,hx e he]

lemma conserved_supported_acyclic (hN : N.Simple) (S : Finset E)
    (ha : (N.restrict (Subtype.val : S → E)).graph.IsAcyclic)
    (x : E → ℝ) (hx : N.boundary x = 0) (hs : ∀ e, e ∉ S → x e = 0) : x = 0 := by
  have hz : (N.restrict (Subtype.val : S → E)).boundary (fun e => x e.val) = 0 := by
    rw [boundary_restrict,extend_restriction S x hs,hx]
  have hh := (N.restrict (Subtype.val : S → E)).acyclic_conserved_zero
    (hN.restrict N _ Subtype.val_injective) ha _ hz
  rw [← extend_restriction S x hs,hh,map_zero]

variable {F : Type*} [Fintype F] (D : Network F E)
omit [Fintype V] in
lemma Duality.complement_connected (h : N.Duality D) (hD : D.Simple) (S : Finset E)
    (ha : (D.restrict (Subtype.val : S → E)).graph.IsAcyclic) :
    (N.restrict (Subtype.val : ↥(Sᶜ) → E)).graph.Connected := by
  have : Nonempty V := h.connected.nonempty
  apply (N.restrict (Subtype.val : ↥(Sᶜ) → E)).connected_of_kernel_constants
  intro f hf v w
  have hz : D.boundary (N.gradient f) = 0 := by
    rw [← LinearMap.mem_ker,h.dual_cycles_eq_cuts]
    exact ⟨f,rfl⟩
  have hs : ∀ e, e ∉ S → N.gradient f e = 0 := by
    intro e he
    exact congrFun hf ⟨e,Finset.mem_compl.mpr he⟩
  exact N.gradient_zero_reachable (D.conserved_supported_acyclic hD S ha _ hz hs) (h.connected v w)

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

lemma boundary_injective_of_tree_card (hc : N.graph.Connected)
    (he : Fintype.card E + 1 = Fintype.card V) : Function.Injective N.boundary := by
  have hh := N.dim_cycles hc
  have hz : Module.finrank ℝ N.boundary.ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)

end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

omit [Fintype F] in
lemma pair_val_ne (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    P.left.val t ≠ P.right.val t := fun h => P.partner t ((State.value_eq_iff _ _ _).mpr h)

omit [Fintype F] in
lemma q_graph (P : (M.system root).Pair (M.nonroots root)) :
    (M.QNet P).graph = (M.system root).oppositeGraph P.right := by
  ext v w
  rw [(M.system root).oppositeGraph_adj_iff P.partner]
  constructor
  · rintro ⟨_,t,h|h⟩
    · exact ⟨t,Or.inl ⟨h.1.symm,h.2.symm⟩⟩
    · exact ⟨t,Or.inr ⟨h.1.symm,h.2.symm⟩⟩
  · rintro ⟨t,h|h⟩
    all_goals have hn := (thirdIndex_distinct _ _ (M.pair_val_ne P t)).1
    · exact ⟨fun he => hn ((M.face t.val).corner_injective (h.2.symm.trans (he.symm.trans h.1))),
        t,Or.inl ⟨h.1.symm,h.2.symm⟩⟩
    · exact ⟨fun he => hn ((M.face t.val).corner_injective (h.2.symm.trans (he.trans h.1))),
        t,Or.inr ⟨h.1.symm,h.2.symm⟩⟩

omit [Fintype F] in
lemma qLabel_ends (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    s(D.tail (M.qLabel P t),D.head (M.qLabel P t)) =
      s((M.QNet P).tail t,(M.QNet P).head t) :=
  (M.face t.val).side_ends D (thirdIndex_distinct _ _ (M.pair_val_ne P t)).1.symm

omit [Fintype F] in
lemma qLabel_black (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    N.blackEndpoint M.black (M.qLabel P t) = t.val :=
  N.blackEndpoint_eq M.black M.coloring t.property.1
    ((N.mem_star _ _).mp ((M.face t.val).side_mem D _ _))

omit [Fintype F] in
lemma qLabel_inj (P : (M.system root).Pair (M.nonroots root)) :
    Function.Injective (M.qLabel P) := by
  intro t u h
  apply Subtype.ext
  exact (M.qLabel_black P t).symm.trans ((congrArg (N.blackEndpoint M.black) h).trans (M.qLabel_black P u))

lemma rootStart_inj (i : Fin 3) : Function.Injective (rootStart i) := by revert i; decide
lemma rootStart_ne (i : Fin 3) (j : Fin 2) : rootStart i j ≠ i+2 := by revert i j; decide

omit [Fintype F] in
lemma augQ_acyclic (P : (M.system root).Pair (M.nonroots root))
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    (M.augQ P i).graph.IsAcyclic := by
  apply (M.QNet P).addSink_acyclic (M.q_graph P ▸ ha) P.left.value_injective _
    ((M.face root).corner_injective.comp (rootStart_inj i))
  · intro t j h
    exact P.left.value_mem t ⟨rootStart i j,h.symm⟩
  · rintro ⟨t|j,h⟩
    · exact P.left.value_mem t ⟨i+2,h.symm⟩
    · exact rootStart_ne i j ((M.face root).corner_injective h)

omit [Fintype F] in
lemma augLabel_ends (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3)
    (t : M.Black root ⊕ Fin 2) :
    s(D.tail (M.augLabel P i t),D.head (M.augLabel P i t)) =
      s((M.augQ P i).tail t,(M.augQ P i).head t) := by
  cases t with
  | inl t => exact M.qLabel_ends P t
  | inr j => exact (M.face root).side_ends D (rootStart_ne i j)

omit [Fintype F] in
lemma augLabel_inj (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) : Function.Injective (M.augLabel P i) := by
  have hb (j : Fin 2) : N.blackEndpoint M.black (M.augLabel P i (.inr j)) = root :=
    N.blackEndpoint_eq M.black M.coloring hr ((N.mem_star _ _).mp ((M.face root).side_mem D _ _))
  rintro (t|j) (u|k) he
  · exact congrArg Sum.inl (M.qLabel_inj P he)
  · have hh := congrArg (N.blackEndpoint M.black) he
    change N.blackEndpoint M.black (M.qLabel P t) = _ at hh
    rw [M.qLabel_black P t,hb] at hh
    exact (t.property.2 hh).elim
  · have hh := congrArg (N.blackEndpoint M.black) he
    change _ = N.blackEndpoint M.black (M.qLabel P u) at hh
    rw [hb,M.qLabel_black P u] at hh
    exact (u.property.2 hh.symm).elim
  · have hh := (M.augLabel_ends P i (.inr j)).symm.trans
      ((congrArg (fun e => s(D.tail e,D.head e)) he).trans (M.augLabel_ends P i (.inr k)))
    rcases Sym2.eq_iff.mp hh with h|h
    · exact congrArg Sum.inr (rootStart_inj i ((M.face root).corner_injective h.1))
    · exact (rootStart_ne i j ((M.face root).corner_injective h.1)).elim

omit [Fintype F] in
lemma removed_acyclic (P : (M.system root).Pair (M.nonroots root))
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    (D.restrict (Subtype.val : M.removed P i → E)).graph.IsAcyclic := by
  apply SimpleGraph.IsAcyclic.anti ?_ (M.augQ_acyclic P ha i)
  rintro v w ⟨hv,e,he⟩
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp e.property
  refine ⟨hv,k,?_⟩
  apply Sym2.eq_iff.mp
  have hh : s(D.tail e.val,D.head e.val) = s(v,w) := Sym2.eq_iff.mpr he
  rw [← hk,M.augLabel_ends] at hh
  exact hh

lemma remainder_connected (P : (M.system root).Pair (M.nonroots root))
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    (N.restrict (Subtype.val : ↥((M.removed P i)ᶜ) → E)).graph.Connected :=
  M.duality.complement_connected N D M.dual_simple _ (M.removed_acyclic P ha i)

omit [Fintype F] in
lemma removed_card (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root) (i : Fin 3) :
    (M.removed P i).card = (Finset.univ.filter M.black).card + 1 := by
  rw [removed,Finset.card_image_of_injective _ (M.augLabel_inj P hr i),Finset.card_univ,Fintype.card_sum]
  have hb : Fintype.card (M.Black root) + 1 = (Finset.univ.filter M.black).card := by
    rw [Fintype.card_subtype]
    have he : (Finset.univ.filter fun v => M.black v ∧ v ≠ root) =
        (Finset.univ.filter M.black).erase root := by ext; simp [and_comm]
    rw [he,Finset.card_erase_add_one (by simp [hr])]
  change Fintype.card (M.Black root) + 2 = _
  omega
end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (D : Network V E)

lemma Triangle.edge_incident {S : Finset E} (t : D.Triangle S) (i j : Fin 3) :
    D.Incident (t.edge i) (t.corner j) ↔ j = i ∨ j = i+1 := by
  rw [D.incident_iff_mem_pair,t.edge_ends,Sym2.mem_iff]
  exact or_congr t.corner_injective.eq_iff t.corner_injective.eq_iff

lemma Triangle.opposite_characteristic {S : Finset E} (t : D.Triangle S)
    {a b : Fin 3} (hab : a ≠ b) {e : E} (he : e ∈ S) :
    e ≠ t.side D a (Barnette.TriangleSystem.thirdIndex a b) ↔ D.Incident e (t.corner b) := by
  have he' := he
  rw [← t.edge_range] at he'
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he'
  rw [t.edge_incident]
  have hh : ∀ a b k : Fin 3, a ≠ b →
      (k ≠ (if Barnette.TriangleSystem.thirdIndex a b = a+1 then a else Barnette.TriangleSystem.thirdIndex a b) ↔
        b = k ∨ b = k+1) := by decide
  have hs (a b : Fin 3) : t.side D a b = t.edge (if b = a+1 then a else b) := by
    unfold Triangle.side; split_ifs <;> rfl
  simp only [hs, ne_eq, t.edge_injective.eq_iff]
  exact hh a b k hab

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

lemma cubic_cards : Fintype.card E = 3*(Finset.univ.filter M.black).card ∧
    Fintype.card V = 2*(Finset.univ.filter M.black).card := by
  have hdeg : ∀ v, N.graph.degree v = 3 := M.cubic
  have he := N.black_edge_partition M.black M.coloring Finset.univ
  simp only [Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _),N.card_star M.simple,
    hdeg,Finset.sum_const,smul_eq_mul,Finset.card_univ] at he
  have hf := N.black_dual_card D M.duality M.simple M.cubic M.black M.coloring
  have heu := M.duality.euler N D
  constructor <;> omega

lemma remainder_independent (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    Function.Injective (N.restrict (Subtype.val : ↥((M.removed P i)ᶜ) → E)).boundary := by
  apply boundary_injective_of_tree_card _ (M.remainder_connected P ha i)
  rw [Fintype.card_coe]
  have hc := Finset.card_add_card_compl (M.removed P i)
  rw [M.removed_card P hr i] at hc
  have hE := M.cubic_cards.1
  have hV := M.cubic_cards.2
  omega

omit [Fintype F] in
lemma remainder_incident (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (t : M.Black root) {e : E} (he : e ∈ N.star t.val)
    (hm : e ∈ (M.removed P i)ᶜ) : D.Incident e (P.right.value t) := by
  have hn := (not_congr (M.removed_at_black P hr i t.val t.property.1 he)).mp (Finset.mem_compl.mp hm)
  simp only [dite_eq_right t.property.2] at hn
  exact ((M.face t.val).opposite_characteristic D (M.pair_val_ne P t) he).mp hn

end
end Barnette.Network.ColoredDual

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.ForestMatching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! From opposite forests to connected spanning matching complements. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
lemma sum_substars (hN : N.Simple) (P : Finset E) (A : Finset V) :
    ∑ v ∈ A, ((N.star v).filter fun e => e ∈ P).card =
      ∑ e, if e ∈ P then ((if N.tail e ∈ A then 1 else 0) + (if N.head e ∈ A then 1 else 0)) else 0 := by
  calc
    _ = ∑ v ∈ A, ∑ e, if e ∈ P then ((if N.tail e = v then 1 else 0) + (if N.head e = v then 1 else 0)) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [star,Finset.filter_filter,Finset.card_filter]
      simp only [Incident]
      apply Finset.sum_congr rfl
      intro e _
      have hne := hN.loopless e
      by_cases hp : e ∈ P <;> by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hp : e ∈ P <;> simp [hp,Finset.sum_add_distrib]

lemma matching_cut_balance (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1)
    (A : Finset V) (hcut : N.cut A ⊆ P) :
    (N.cut A).card = 2*(N.blackCut black A).card := by
  have hsum := N.sum_substars hN P A
  simp only [hd,Finset.sum_const,smul_eq_mul,mul_one] at hsum
  have htotal : A.card + (N.cut A).card = 2*((N.regionEdges A).filter fun e => e ∈ P).card := by
    rw [hsum]
    simp only [cut,regionEdges,Finset.card_filter,Finset.sum_filter,
      ← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    have hh : (N.tail e ∈ A ∧ N.head e ∉ A ∨ N.head e ∈ A ∧ N.tail e ∉ A) → e ∈ P := by
      intro hh; apply hcut; simpa [cut] using hh
    by_cases ht : N.tail e ∈ A <;> by_cases hh' : N.head e ∈ A <;> by_cases hp : e ∈ P <;> simp_all
  have hbsum := N.sum_substars hN P (A.filter black)
  simp only [hd,Finset.sum_const,smul_eq_mul,mul_one] at hbsum
  have hblack : (A.filter black).card + (N.cut A).card =
      ((N.regionEdges A).filter fun e => e ∈ P).card + (N.blackCut black A).card := by
    rw [hbsum]
    simp only [cut,regionEdges,blackCut,Finset.card_filter,Finset.mem_filter,Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have hh : (N.tail e ∈ A ∧ N.head e ∉ A ∨ N.head e ∈ A ∧ N.tail e ∉ A) → e ∈ P := by
      intro hh; apply hcut; simpa [cut] using hh
    have hc' := hc e
    by_cases ht : N.tail e ∈ A <;> by_cases hh' : N.head e ∈ A <;>
      by_cases hp : e ∈ P <;> by_cases hb : black (N.tail e) <;> by_cases hw : black (N.head e) <;>
      simp_all [blackEndpoint]
  have hcub := N.cubic_region_count hN h3 A
  have hbcub := N.cubic_black_region_count hN h3 black hc A
  omega
end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

lemma black_white_balance : Fintype.card {v // M.black v} = Fintype.card {v // ¬M.black v} := by
  have hc := M.cubic_cards.2
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_subtype]
  change (Finset.univ.filter M.black).card = Fintype.card V - (Finset.univ.filter M.black).card
  omega

lemma recovery_matching (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    ∃ S : Finset E, S ⊆ (M.removed P i)ᶜ ∧ ∀ v, ((N.star v).filter fun e => e ∈ S).card = 1 :=
  N.tree_matching M.black M.coloring _ (M.remainder_independent P hr ha i) root hr
    (M.remainder_black_degree P hr i) M.black_white_balance

end
end Barnette.Network.ColoredDual
namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
variable {V E : Type*} (N : Network V E)
lemma directed_cycle_of_not_acyclic (ht : Function.Injective N.tail) (hn : ¬N.graph.IsAcyclic) :
    ∃ (C : Barnette.CycleCoordinates N.graph) (e : Fin (C.n+3) → E),
      ∀ i, N.tail (e i) = C.vertex i ∧ N.head (e i) = C.vertex (i+1) := by
  obtain ⟨C⟩ := Barnette.cycleCoordinates_of_not_acyclic hn
  let e : Fin (C.n+3) ↪ E := ⟨N.cycleEdge C,N.cycleEdge_injective C⟩
  have he (i) : (N.tail (e i) = C.vertex i ∧ N.head (e i) = C.vertex (i+1)) ∨
      (N.tail (e i) = C.vertex (i+1) ∧ N.head (e i) = C.vertex i) :=
    Sym2.eq_iff.mp (N.cycleEdge_ends C i)
  rcases C.tail_orientation e N.tail ht (fun i => (he i).elim (Or.inl ∘ And.left) (Or.inr ∘ And.left)) with hf|hb
  · refine ⟨C,e,fun i => ⟨hf i,?_⟩⟩
    rcases he i with h|h
    · exact h.2
    · exact ((C.adjacent i).1 ((hf i).symm.trans h.1)).elim
  · refine ⟨C.reverseCycle,fun i => e (-i-1),fun i => ?_⟩
    have hh : N.head (e (-i-1)) = C.vertex (-i-1) := by
      rcases he (-i-1) with h|h
      · exact ((C.adjacent (-i-1)).1 (h.1.symm.trans (hb (-i-1)))).elim
      · exact h.2
    constructor
    · change N.tail (e (-i-1)) = C.vertex (-i)
      simpa only [sub_add_cancel] using hb (-i-1)
    · change N.head (e (-i-1)) = C.vertex (-(i+1))
      exact hh.trans (congrArg C.vertex (show -i-1 = -(i+1) by abel))
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype E] (N : Network V E)

lemma matchingEdge_spec (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (v : V) :
    (N.star v).filter (fun e => e ∈ P) = {N.matchingEdge P hd v} :=
  (Finset.card_eq_one.mp (hd v)).choose_spec

lemma matchingEdge_mem (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (v : V) :
    N.matchingEdge P hd v ∈ N.star v ∧ N.matchingEdge P hd v ∈ P := by
  exact Finset.mem_filter.mp (by rw [N.matchingEdge_spec P hd v]; exact Finset.mem_singleton_self _)

lemma matchingEdge_eq (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1)
    {v : V} {e : E} (he : e ∈ N.star v) (hp : e ∈ P) : e = N.matchingEdge P hd v := by
  exact Finset.mem_singleton.mp ((N.matchingEdge_spec P hd v) ▸ Finset.mem_filter.mpr ⟨he,hp⟩)
end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

lemma selectNet_forest (s : M.State root) (P : Finset E)
    (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1)
    (hi : ∀ t : M.Black root, D.Incident (N.matchingEdge P hd t.val) (s.value t)) :
    (M.selectNet s P hd).graph.IsAcyclic := by
  by_contra hn
  obtain ⟨C,t,ht⟩ := (M.selectNet s P hd).directed_cycle_of_not_acyclic s.value_injective hn
  have he (i) : s(D.tail (N.matchingEdge P hd (t i).val),D.head (N.matchingEdge P hd (t i).val)) =
      s(C.vertex i,C.vertex (i+1)) := by
    rw [(D.otherEnd_spec M.dual_simple (hi (t i))).2]
    change s((M.selectNet s P hd).tail (t i),(M.selectNet s P hd).head (t i)) = _
    rw [(ht i).1,(ht i).2]
  let C' : Barnette.CycleCoordinates D.graph := {
    n := C.n
    vertex := C.vertex
    adjacent i := ⟨(C.adjacent i).1,N.matchingEdge P hd (t i).val,Sym2.eq_iff.mp (he i)⟩ }
  have hedge (i) : D.cycleEdge C' i = N.matchingEdge P hd (t i).val := by
    apply M.dual_simple.pair_injective
    dsimp only
    rw [D.cycleEdge_ends]
    exact (he i).symm
  obtain ⟨A,c,_,_,_,_,hcut,hcount,_⟩ := M.cycle_disk s C' t
    (fun i => hedge i ▸ (N.matchingEdge_mem P hd (t i).val).1) (fun i => (ht i).1)
  have hsub : N.cut A ⊆ P := by
    intro e he
    rw [hcut] at he
    obtain ⟨i,rfl⟩ := (D.mem_cycleEdges C' e).mp he
    rw [hedge]
    exact (N.matchingEdge_mem P hd (t i).val).2
  have hbal := N.matching_cut_balance M.simple M.cubic M.black M.coloring P hd A hsub
  omega

lemma selected_forest (s : M.State root) (P : Finset E)
    (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (_hr : M.black root)
    (hi : ∀ t : M.Black root, D.Incident (N.matchingEdge P hd t.val) (s.value t))
    (i : Fin 3) (he0 : N.matchingEdge P hd root = (M.face root).edge i) :
    (D.restrict (Subtype.val : P → E)).graph.IsAcyclic := by
  let L := M.selectNet s P hd
  let K := L.addSink (fun j => (M.face root).corner (rootStart (i+2) j)) ((M.face root).corner (i+2+2))
  have hK : K.graph.IsAcyclic := by
    apply L.addSink_acyclic (M.selectNet_forest s P hd hi) s.value_injective _
      ((M.face root).corner_injective.comp (rootStart_inj (i+2)))
    · intro t j h
      exact s.value_mem t ⟨rootStart (i+2) j,h.symm⟩
    · rintro ⟨t|j,h⟩
      · exact s.value_mem t ⟨i+2+2,h.symm⟩
      · exact rootStart_ne (i+2) j ((M.face root).corner_injective h)
  apply SimpleGraph.IsAcyclic.anti ?_ hK
  intro v w ⟨hvw,e,he⟩
  let b := N.blackEndpoint M.black e.val
  have hb : M.black b := (N.blackEndpoint_spec M.black M.coloring e.val).1
  have heb : e.val ∈ N.star b := (N.mem_star _ _).mpr (N.blackEndpoint_spec M.black M.coloring e.val).2
  have hep : e.val = N.matchingEdge P hd b := N.matchingEdge_eq P hd heb e.property
  have hends : s(D.tail e.val,D.head e.val) = s(v,w) := Sym2.eq_iff.mpr he
  by_cases hbr : b = root
  · have hstart : rootStart (i+2) 1 = i := by fin_cases i <;> rfl
    have hend : i+2+2 = i+1 := by fin_cases i <;> rfl
    refine ⟨hvw,Sum.inr 1,?_⟩
    apply Sym2.eq_iff.mp
    change s((M.face root).corner (rootStart (i+2) 1),(M.face root).corner (i+2+2)) = s(v,w)
    rw [hstart,hend,← (M.face root).edge_ends i,← he0,← hbr,← hep]
    exact hends
  · let t : M.Black root := ⟨b,hb,hbr⟩
    refine ⟨hvw,Sum.inl t,?_⟩
    apply Sym2.eq_iff.mp
    change s(s.value t,D.otherEnd (N.matchingEdge P hd b) (s.value t)) = s(v,w)
    rw [← (D.otherEnd_spec M.dual_simple (hi t)).2,← hep]
    exact hends

lemma recover_connected_complement (Q : (M.system root).Pair (M.nonroots root))
    (hr : M.black root) (ha : ((M.system root).oppositeGraph Q.right).IsAcyclic) (i : Fin 3) :
    ∃ P : Finset E, (M.face root).edge i ∈ P ∧
      (∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) ∧
      (N.restrict (Subtype.val : ↥(Pᶜ) → E)).graph.Connected := by
  obtain ⟨P,hsub,hd⟩ := M.recovery_matching Q hr ha i
  have hi (t : M.Black root) : D.Incident (N.matchingEdge P hd t.val) (Q.right.value t) :=
    M.remainder_incident Q hr i t (N.matchingEdge_mem P hd t.val).1
      (hsub (N.matchingEdge_mem P hd t.val).2)
  have he0 : N.matchingEdge P hd root = (M.face root).edge i := by
    have hmem := (N.matchingEdge_mem P hd root)
    have hm := M.removed_at_black Q hr i root hr hmem.1
    have hn := (not_congr hm).mp (Finset.mem_compl.mp (hsub hmem.2))
    simpa using hn
  refine ⟨P,he0 ▸ (N.matchingEdge_mem P hd root).2,hd,?_⟩
  exact M.duality.complement_connected N D M.dual_simple P
    (M.selected_forest Q.right P hd hr hi i he0)
end
end Barnette.Network.ColoredDual

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network OAI.Barnette.Network.ColoredDual
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.ColoredDual.recover_connected_complement := @_root_.OAI.Barnette.Network.ColoredDual.recover_connected_complement
