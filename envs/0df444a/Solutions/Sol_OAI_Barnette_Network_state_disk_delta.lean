-- Prove2me | solution 1 for OAI.Barnette.Network.state_disk_delta
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:47:16.40637+00:00
-- url     : https://prove2.me/submissions/b0e4ff56-0304-439e-b859-602f367ad187

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean:L446-L482
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.state_disk_delta. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_Bond_connected_shore
import Theorems.Thm_OAI_Barnette_Network_Duality_bond_of_circuit
import Theorems.Thm_OAI_Barnette_Network_Duality_circuit_cut
import Theorems.Thm_OAI_Barnette_Network_cubic_black_region_count
import Theorems.Thm_OAI_Barnette_Network_cubic_region_count
import Theorems.Thm_OAI_Barnette_Network_flowCircuit_of_cycle
import Theorems.Thm_OAI_Barnette_Network_region_connected
import Theorems.Thm_OAI_Barnette_Network_region_cycles_eq_range
import Theorems.Thm_OAI_Barnette_Network_state_disk_count

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
omit [Fintype V] in
lemma boundary_basis (e : E) : N.boundary (basisVec e) = fun v => N.incidence v e := by
  ext v
  rw [boundary_apply, Finset.sum_eq_single e]
  · simp [basisVec, incidence]
  · intro k _ hke; simp [basisVec, hke]
  · simp

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

-- ---- from OAI.Combinatorics.Hamiltonian.Bonds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Cycle flows, minimal cuts, and connected shores. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] [Fintype E] in
lemma arcSign_ne_zero (e : E) (v : V) : N.arcSign e v ≠ 0 := by
  simp only [arcSign]; split_ifs <;> norm_num

omit [Fintype V] in
lemma boundary_directed_unit {e : E} {v w : V} (hne : v ≠ w)
    (he : s(N.tail e,N.head e) = s(v,w)) :
    N.boundary (N.arcSign e v • basisVec e) =
      fun z => (if z = w then 1 else 0) - (if z = v then 1 else 0) := by
  rw [map_smul, N.boundary_basis]
  ext z
  rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩
  · simp only [Pi.smul_apply, smul_eq_mul, incidence, arcSign, ht, hh, ite_true, one_mul]
    congr 1 <;> simp only [eq_comm]
  · have htv : N.tail e ≠ v := by rw [ht]; exact hne.symm
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [arcSign, ite_eq_right htv]
    simp only [incidence, ht, hh, neg_one_mul, neg_sub]
    congr 1 <;> simp only [eq_comm]

omit [Fintype V] in
lemma cycleFlow_conserved : N.boundary (N.cycleFlow C) = 0 := by
  rw [cycleFlow,map_sum]
  have hi (i : Fin (C.n+3)) :
      N.boundary (N.arcSign (N.cycleEdge C i) (C.vertex i) • basisVec (N.cycleEdge C i)) =
        fun z => (if z = C.vertex (i+1) then 1 else 0) - (if z = C.vertex i then 1 else 0) :=
    N.boundary_directed_unit (C.adjacent i).ne (N.cycleEdge_ends C i)
  simp_rw [hi]
  ext z
  simp only [Finset.sum_apply, Pi.zero_apply, Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin (C.n+3))) (fun i => if z = C.vertex i then (1:ℝ) else 0)

omit [Fintype V] [Fintype E] in
lemma cycleFlow_apply_edge (i : Fin (C.n+3)) :
    N.cycleFlow C (N.cycleEdge C i) = N.arcSign (N.cycleEdge C i) (C.vertex i) := by
  simp only [cycleFlow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVec]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : N.cycleEdge C i ≠ N.cycleEdge C j := fun h => hji ((N.cycleEdge_injective C h).symm)
    simp [hne]
  · simp

omit [Fintype V] [Fintype E] in
lemma cycleFlow_zero_outside {e : E} (he : e ∉ N.cycleEdges C) : N.cycleFlow C e = 0 := by
  have hi : ∀ i, e ≠ N.cycleEdge C i := by
    intro i h
    apply he
    exact (N.mem_cycleEdges C e).mpr ⟨i,h.symm⟩
  simp only [cycleFlow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVec, hi,
    ite_false, mul_zero, Finset.sum_const_zero]

omit [Fintype V] in
lemma cycleFlow_support : N.flowSupport (N.cycleFlow C) = N.cycleEdges C := by
  ext e
  constructor
  · intro he
    by_contra hn
    exact (N.mem_flowSupport _ _).mp he (N.cycleFlow_zero_outside C hn)
  · intro he
    obtain ⟨i,rfl⟩ := (N.mem_cycleEdges C e).mp he
    rw [mem_flowSupport, N.cycleFlow_apply_edge]
    exact N.arcSign_ne_zero _ _

omit [Fintype V] in
lemma cycleFlow_circuit (hN : N.Simple) : N.FlowCircuit (N.cycleFlow C) :=
  N.flowCircuit_of_cycle C hN _ (N.cycleFlow_conserved C) (N.cycleFlow_support C)

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

-- ---- from OAI.Combinatorics.Hamiltonian.Quotients ----
namespace OAI

/-! Vertex quotients and connected fibers of incidence networks. -/

namespace Barnette.Network
noncomputable section
variable {V W E K : Type*}
open scoped Classical

variable [Fintype V] [Fintype W] [Fintype E] [Fintype K]

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
lemma regionCycleMap_injective (hN : N.graph.Connected) (A : Finset V)
    (hout : ∃ v, v ∉ A) : Function.Injective (N.regionCycleMap A) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  have hz : N.regionCycleMap A f = 0 := hf
  have hg : N.gradient (push (Subtype.val : A → V) f) = 0 := by
    rw [← N.extend_restrict_gradient A f]
    change push (Subtype.val : N.regionEdges A → E) (N.regionCycleMap A f) = 0
    rw [hz,map_zero]
  obtain ⟨r,hr⟩ := hout
  ext v
  have he := N.gradient_zero_reachable hg (hN r v.val)
  rw [push_subtype_outside A f hr, push_subtype_apply A f v] at he
  exact he.symm

omit [Fintype V] in
lemma region_dim_cycles (h : N.Duality D) (A : Finset V)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected) :
    Module.finrank ℝ (N.region D A).boundary.ker = A.card := by
  rw [N.region_cycles_eq_range D h A hAc,
    LinearMap.finrank_range_of_inj (N.regionCycleMap_injective h.connected A ?_),
    Module.finrank_pi,Fintype.card_coe]
  obtain ⟨v⟩ := hAc.nonempty
  exact ⟨v.val,v.property⟩

omit [Fintype V] in

theorem region_euler (h : N.Duality D) (A : Finset V)
    (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) :
    A.card + (N.regionVertices D A).card = (N.regionEdges A).card + 1 := by
  have hh := (N.region D A).dim_cycles (N.region_connected D A hA sD face)
  rwa [N.region_dim_cycles D h A hAc,Fintype.card_coe,Fintype.card_coe] at hh

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

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma blackDelta_cut (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (C : Barnette.CycleCoordinates D.graph) (A : Finset V) (c : ℝ)
    (hx : D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0))
    (hcut : N.cut A = D.cycleEdges C) :
    N.blackDelta D black C = c * (2 * (N.blackCut black A).card - (N.cut A).card) := by
  have hsum : N.blackDelta D black C = ∑ e ∈ N.cut A,
      N.gradient (fun v => if black v then 1 else 0) e * D.cycleFlow C e := by
    rw [hcut,cycleEdges,Finset.sum_image (D.cycleEdge_injective C).injOn]
    simp only [blackDelta,D.cycleFlow_apply_edge]
  rw [hsum]
  simp only [hx,Pi.smul_apply,smul_eq_mul]
  have heq (e : E) (he : e ∈ N.cut A) :
      N.gradient (fun v => if black v then (1:ℝ) else 0) e *
        (c * N.gradient (fun v => if v ∈ A then 1 else 0) e) =
      c * (2 * (if N.blackEndpoint black e ∈ A then 1 else 0) - 1) := by
    have hcol := hc e
    have he' := (N.mem_cut A e).mp he
    by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;>
      by_cases hb : black (N.tail e) <;> by_cases hw : black (N.head e) <;>
      simp_all [gradient_apply,blackEndpoint] <;> ring
  rw [Finset.sum_congr rfl heq,← Finset.mul_sum,Finset.sum_sub_distrib,
    ← Finset.mul_sum,Finset.sum_boole]
  simp [blackCut]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma cycle_cut_scalar (C : Barnette.CycleCoordinates D.graph) (A : Finset V) (c : ℝ)
    (hx : D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0)) :
    c = 1 ∨ c = -1 := by
  have hh := congrFun hx (D.cycleEdge C 0)
  rw [D.cycleFlow_apply_edge] at hh
  simp only [Pi.smul_apply,smul_eq_mul,gradient_apply] at hh
  by_cases ht : N.tail (D.cycleEdge C 0) ∈ A <;>
    by_cases hh' : N.head (D.cycleEdge C 0) ∈ A <;>
    by_cases hd : D.tail (D.cycleEdge C 0) = C.vertex 0 <;>
    simp [arcSign,ht,hh',hd] at hh <;>
    first | exact Or.inl (by linarith) | exact Or.inr (by linarith)

lemma disk_boundary_imbalance (h : N.Duality D) (sN : N.Simple)
    (hdeg : N.graph.IsRegularOfDegree 3) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v))
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected)
    (hm : (A.filter black).card + (N.cut A).card =
      (N.regionVertices D A).card + (N.blackCut black A).card) :
    (N.cut A).card = 2 * (N.blackCut black A).card + 3 := by
  have he := N.region_euler D h A hA hAc sD face
  have ht := N.cubic_region_count sN hdeg A
  have hb := N.cubic_black_region_count sN hdeg black hc A
  omega

theorem state_disk_delta (h : N.Duality D) (sN : N.Simple)
    (hdeg : N.graph.IsRegularOfDegree 3) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (root : V)
    (m : V → F)
    (hm_inj : Set.InjOn m {v | black v ∧ v ≠ root})
    (hm_face : ∀ v, black v → v ≠ root → m v ∈ Set.range (face v).corner)
    (hm_range : ∀ z, z ∉ Set.range (face root).corner ↔
      ∃ v, black v ∧ v ≠ root ∧ m v = z)
    (C : Barnette.CycleCoordinates D.graph)
    (hchoice : ∀ i, N.blackEndpoint black (D.cycleEdge C i) ≠ root ∧
      m (N.blackEndpoint black (D.cycleEdge C i)) = C.vertex i) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ (c = 1 ∨ c = -1) ∧
      D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.cycleEdges C ∧
      (N.cut A).card = 2 * (N.blackCut black A).card + 3 ∧
      N.blackDelta D black C = -3*c := by
  have hx := D.cycleFlow_circuit C sD
  obtain ⟨A,c,ha,hr,_hc0,he,hcut⟩ := h.circuit_cut N D (D.cycleFlow C) hx root
  rw [D.cycleFlow_support] at hcut
  have hb : N.Bond A := h.bond_of_circuit N D (D.cycleFlow C) hx A (by
    rw [D.cycleFlow_support]; exact hcut)
  have hA := hb.connected_shore N h.connected ha ⟨root,hr⟩
  have hAc := hb.compl.connected_shore N h.connected
    (Finset.mem_compl.mpr hr |> fun hh => ⟨root,hh⟩) (by
      obtain ⟨v,hv⟩ := ha
      exact ⟨v,by simpa using hv⟩)
  have hsides : {v : V | v ∈ Aᶜ} = {v : V | v ∉ A} := by
    ext v
    exact Finset.mem_compl
  rw [hsides] at hAc
  have hm := N.state_disk_count D h sD face black hc root m hm_inj hm_face hm_range C hchoice A hr hcut
  have hcount := N.disk_boundary_imbalance D h sN hdeg sD face black hc A hA hAc hm
  refine ⟨A,c,ha,hr,N.cycle_cut_scalar D C A c he,he,hcut,hcount,?_⟩
  rw [N.blackDelta_cut D black hc C A c he hcut,hcount]
  push_cast
  ring

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.state_disk_delta := @_root_.OAI.Barnette.Network.state_disk_delta
