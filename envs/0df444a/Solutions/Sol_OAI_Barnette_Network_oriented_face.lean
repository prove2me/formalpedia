-- Prove2me | solution 1 for OAI.Barnette.Network.oriented_face
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:48:52.875928+00:00
-- url     : https://prove2.me/submissions/df8280c6-cc0b-4329-895c-3c2d168f6b20

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Circulation.lean:L98-L144
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.oriented_face. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_flowCircuit_of_cycle

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

omit [Fintype V] in

lemma FlowCircuit.proportional (x : E → ℝ) (hx : N.FlowCircuit x)
    (y : E → ℝ) (hy : N.boundary y = 0)
    (hs : N.flowSupport y ⊆ N.flowSupport x) : ∃ c : ℝ, y = c • x := by
  obtain ⟨e,he⟩ : ∃ e, x e ≠ 0 := by
    by_contra hn
    apply hx.nonzero
    ext e
    exact not_not.mp (fun he => hn ⟨e,he⟩)
  let c := y e / x e
  let z := y - c • x
  have hz : N.boundary z = 0 := by simp [z,map_sub,map_smul,hy,hx.conserved]
  have hzs : N.flowSupport z ⊆ N.flowSupport x := by
    intro k hk
    by_contra hn
    have hxk : x k = 0 := not_not.mp (by simpa only [mem_flowSupport] using hn)
    have hyk : y k = 0 := by
      by_contra hyk
      exact hn (hs ((N.mem_flowSupport y k).mpr hyk))
    exact (N.mem_flowSupport z k).mp hk (by simp [z,hxk,hyk])
  have hze : z e = 0 := by simp [z,c,div_mul_cancel₀ _ he]
  have hz0 : z = 0 := (hx.minimal z hz hzs).resolve_right (by
    intro hh
    have hem : e ∈ N.flowSupport z := hh ▸ (N.mem_flowSupport x e).mpr he
    exact (N.mem_flowSupport z e).mp hem hze)
  exact ⟨c,sub_eq_zero.mp hz0⟩

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.coordinates_edge (sD : D.Simple) {s : Finset E} (t : D.Triangle s) (i : Fin 3) :
    D.cycleEdge (t.coordinates D) i = t.edge i := by
  apply sD.pair_injective
  exact (D.cycleEdge_ends (t.coordinates D) i).trans (t.edge_ends i).symm

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.coordinates_edges (sD : D.Simple) {s : Finset E} (t : D.Triangle s) :
    D.cycleEdges (t.coordinates D) = s := by
  have hf : D.cycleEdge (t.coordinates D) = t.edge := funext (t.coordinates_edge D sD)
  change Finset.univ.image (D.cycleEdge (t.coordinates D)) = s
  rw [hf]
  exact t.edge_range

omit [Fintype V] [Fintype E] [Fintype F] in
lemma arcSign_opposite {e : E} {v w : F}
    (hne : v ≠ w) (he : s(D.tail e,D.head e) = s(v,w)) :
    D.arcSign e w = - D.arcSign e v := by
  rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩
  · simp [arcSign,ht,hne]
  · simp [arcSign,ht,hne.symm]

omit [Fintype V] [Fintype F] in

theorem oriented_face (h : N.Duality D) (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v)) :
    ∃ u : D.Triangle (N.star v), ∀ i,
      N.gradient (fun w => if w = v then 1 else 0) (u.edge i) =
        D.arcSign (u.edge i) (u.corner i) := by
  let x := D.cycleFlow (t.coordinates D)
  let y := N.gradient (fun w => if w = v then 1 else 0)
  have hx := D.cycleFlow_circuit (t.coordinates D) sD
  have hy := h.dual_conserved_gradient N D (fun w => if w = v then 1 else 0)
  have hs : D.flowSupport y = D.flowSupport x := by
    rw [D.cycleFlow_support,t.coordinates_edges D sD]
    exact N.gradient_indicator_support D sN v
  obtain ⟨c,hc⟩ := hx.proportional D x y hy hs.subset
  have hxi (i : Fin 3) : x (t.edge i) = D.arcSign (t.edge i) (t.corner i) := by
    have hh := D.cycleFlow_apply_edge (t.coordinates D) i
    change x (D.cycleEdge (t.coordinates D) i) = D.arcSign (D.cycleEdge (t.coordinates D) i) (t.corner i) at hh
    rw [t.coordinates_edge D sD i] at hh
    exact hh
  have hci (i : Fin 3) : y (t.edge i) = c * D.arcSign (t.edge i) (t.corner i) := by
    rw [hc,Pi.smul_apply,smul_eq_mul,hxi]
  have he : t.edge 0 ∈ N.star v := by
    have hh : t.edge 0 ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    rwa [t.edge_range] at hh
  have hcv : c = 1 ∨ c = -1 := by
    have hh := hci 0
    have hne := sN.loopless (t.edge 0)
    rcases (N.mem_star _ _).mp he with ht | hh'
    · have hhead : N.head (t.edge 0) ≠ v := fun h => hne (ht.trans h.symm)
      simp only [y,gradient_apply,ht,hhead,ite_true,ite_false,zero_sub] at hh
      by_cases hd : D.tail (t.edge 0) = t.corner 0 <;> simp [arcSign,hd] at hh <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
    · have htail : N.tail (t.edge 0) ≠ v := fun h => hne (h.trans hh'.symm)
      simp only [y,gradient_apply,hh',htail,ite_true,ite_false,sub_zero] at hh
      by_cases hd : D.tail (t.edge 0) = t.corner 0 <;> simp [arcSign,hd] at hh <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
  rcases hcv with rfl | rfl
  · exact ⟨t,fun i => by simpa only [one_mul] using hci i⟩
  · refine ⟨t.reverse D,?_⟩
    intro i
    change y (t.edge (-i-1)) = D.arcSign (t.edge (-i-1)) (t.corner (-i))
    have hh := hci (-i-1)
    have ha := D.arcSign_opposite ((t.coordinates D).adjacent (-i-1 : Fin 3)).ne (t.edge_ends (-i-1))
    change D.arcSign (t.edge (-i-1)) (t.corner (-i-1+1)) =
      - D.arcSign (t.edge (-i-1)) (t.corner (-i-1)) at ha
    rw [sub_add_cancel] at ha
    rw [ha]
    simpa only [neg_one_mul] using hh

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


theorem solution : type_of% @_root_.OAI.Barnette.Network.oriented_face := @_root_.OAI.Barnette.Network.oriented_face
