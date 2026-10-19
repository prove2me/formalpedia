-- Prove2me | solution 1 for OAI.Barnette.Network.state_disk_count
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:45:14.921196+00:00
-- url     : https://prove2.me/submissions/003cda44-b326-44c6-8c5a-e66844846c75

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean:L264-L377
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.state_disk_count. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_Duality_vertex_flow_circuit
import Theorems.Thm_OAI_Barnette_Network_Triangle_corner_iff_incident
import Theorems.Thm_OAI_Barnette_Network_faces_vertex_deleted_connected

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

-- ---- from OAI.Combinatorics.Hamiltonian.StateDisk ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Minimal links, incidence states, and the signed disk identity. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in

lemma cut_restrict_conserved (x : E → ℝ) (hx : N.boundary x = 0) (A : Finset V)
    (hcut : ∀ e ∈ N.cut A, x e = 0) :
    N.boundary (fun e => if N.tail e ∈ A then x e else 0) = 0 := by
  ext v
  have hb : N.boundary (fun e => if N.tail e ∈ A then x e else 0) v =
      if v ∈ A then N.boundary x v else 0 := by
    simp only [boundary_apply]
    trans ∑ e, if v ∈ A then
      ((if N.head e = v then x e else 0) - (if N.tail e = v then x e else 0)) else 0
    swap
    · by_cases hv : v ∈ A <;> simp [hv]
    apply Finset.sum_congr rfl
    intro e _
    have hcross : N.tail e ∈ A ∨ N.head e ∈ A →
        ¬(N.tail e ∈ A ∧ N.head e ∈ A) → x e = 0 := by
      intro h1 h2
      apply hcut e
      rw [N.mem_cut]
      tauto
    by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;>
      by_cases ha : N.tail e ∈ A <;> by_cases hb : N.head e ∈ A <;>
      by_cases hv : v ∈ A <;> simp_all
  rw [hb,hx]
  simp

omit [Fintype V] in

lemma FlowCircuit.no_split (x : E → ℝ) (hx : N.FlowCircuit x) (A : Finset V)
    (hcut : ∀ e ∈ N.cut A, x e = 0)
    {e : E} (he : x e ≠ 0) (heA : N.tail e ∈ A) :
    ∀ k, x k ≠ 0 → N.tail k ∈ A := by
  let y : E → ℝ := fun k => if N.tail k ∈ A then x k else 0
  have hy := N.cut_restrict_conserved x hx.conserved A hcut
  have hs : N.flowSupport y ⊆ N.flowSupport x := by
    intro k hk
    simp only [mem_flowSupport,y] at hk ⊢
    split_ifs at hk <;> tauto
  have hyn : y ≠ 0 := by
    intro hy0
    have hh := congrFun hy0 e
    apply he
    simpa [y,heA] using hh
  have hEq := (hx.minimal y hy hs).resolve_left hyn
  intro k hk
  have hyk := (N.mem_flowSupport y k).mp (by rw [hEq]; exact (N.mem_flowSupport x k).mpr hk)
  by_contra hn
  exact hyk (by simp [y,hn])

theorem mixed_corner_on_boundary (h : N.Duality D) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (A : Finset V) {z : F}
    (hzin : z ∈ N.regionVertices D A) (hzout : z ∈ N.regionVertices D Aᶜ) :
    ∃ e ∈ N.cut A, D.Incident e z := by
  by_contra hn
  have hc := h.vertex_flow_circuit N D z
    (faces_vertex_deleted_connected N D h.connected h.dual_connected sD face z)
  let x := D.gradient (fun w => if w = z then (1:ℝ) else 0)
  have hs : N.flowSupport x = D.star z := D.gradient_indicator_support N sD z
  have hcut : ∀ e ∈ N.cut A, x e = 0 := by
    intro e he
    by_contra hx
    have hh : D.Incident e z := (D.mem_star e z).mp (by
      rw [← hs]; exact (N.mem_flowSupport x e).mpr hx)
    exact hn ⟨e,he,hh⟩
  obtain ⟨e,he,hez⟩ := (N.mem_regionVertices D A z).mp hzin
  have hex : x e ≠ 0 := (N.mem_flowSupport x e).mp (by rw [hs]; exact (D.mem_star e z).mpr hez)
  have heA : N.tail e ∈ A := by
    rcases (N.mem_regionEdges A e).mp he with ht | hh
    · exact ht
    · by_contra ht
      exact hex (hcut e ((N.mem_cut A e).mpr (Or.inr ⟨hh,ht⟩)))
  have hall := hc.no_split N x A hcut hex heA
  obtain ⟨k,hk,hkz⟩ := (N.mem_regionVertices D Aᶜ z).mp hzout
  have hkx : x k ≠ 0 := (N.mem_flowSupport x k).mp (by rw [hs]; exact (D.mem_star k z).mpr hkz)
  have hkA := hall k hkx
  rcases (N.mem_regionEdges Aᶜ k).mp hk with ht | hh
  · exact (Finset.mem_compl.mp ht) hkA
  · exact hkx (hcut k ((N.mem_cut A k).mpr (Or.inl ⟨hkA,Finset.mem_compl.mp hh⟩)))

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma mem_cycleVertices (C : Barnette.CycleCoordinates D.graph) (z : F) :
    z ∈ D.cycleVertices C ↔ ∃ i, C.vertex i = z := by
  simp [cycleVertices]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma incident_cycle_iff (C : Barnette.CycleCoordinates D.graph) (z : F) :
    (∃ e ∈ D.cycleEdges C, D.Incident e z) ↔ z ∈ D.cycleVertices C := by
  constructor
  · rintro ⟨e,he,hz⟩
    obtain ⟨i,rfl⟩ := (D.mem_cycleEdges C e).mp he
    rw [D.incident_iff_mem_pair,D.cycleEdge_ends,Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact (D.mem_cycleVertices C _).mpr ⟨i,rfl⟩
    · exact (D.mem_cycleVertices C _).mpr ⟨i+1,rfl⟩
  · intro hz
    obtain ⟨i,rfl⟩ := (D.mem_cycleVertices C z).mp hz
    refine ⟨D.cycleEdge C i,(D.mem_cycleEdges C _).mpr ⟨i,rfl⟩,?_⟩
    rw [D.incident_iff_mem_pair,D.cycleEdge_ends]; simp

omit [Fintype V] in
lemma regionVertices_iff_face (face : ∀ v, D.Triangle (N.star v))
    (A : Finset V) (z : F) :
    z ∈ N.regionVertices D A ↔ ∃ v ∈ A, z ∈ Set.range (face v).corner := by
  constructor
  · intro hz
    obtain ⟨e,he,hez⟩ := (N.mem_regionVertices D A z).mp hz
    rcases (N.mem_regionEdges A e).mp he with ht | hh
    · exact ⟨N.tail e,ht,((face _).corner_iff_incident D z).mpr
        ⟨e,(N.mem_star e _).mpr (Or.inl rfl),hez⟩⟩
    · exact ⟨N.head e,hh,((face _).corner_iff_incident D z).mpr
        ⟨e,(N.mem_star e _).mpr (Or.inr rfl),hez⟩⟩
  · rintro ⟨v,hv,hz⟩
    obtain ⟨e,he,hez⟩ := ((face v).corner_iff_incident D z).mp hz
    refine (N.mem_regionVertices D A z).mpr ⟨e,?_,hez⟩
    rcases (N.mem_star e v).mp he with ht | hh
    · exact (N.mem_regionEdges A e).mpr (Or.inl (ht ▸ hv))
    · exact (N.mem_regionEdges A e).mpr (Or.inr (hh ▸ hv))

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackEndpoint_spec (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    black (N.blackEndpoint black e) ∧ N.Incident e (N.blackEndpoint black e) := by
  by_cases ht : black (N.tail e)
  · simp only [blackEndpoint,ite_eq_left ht]; exact ⟨ht,Or.inl rfl⟩
  · simp only [blackEndpoint,ite_eq_right ht]
    exact ⟨not_not.mp (fun hh => ht ((hc e).mpr hh)),Or.inr rfl⟩

theorem state_disk_count (h : N.Duality D) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (root : V)
    (m : V → F)
    (hm_inj : Set.InjOn m {v | black v ∧ v ≠ root})
    (hm_face : ∀ v, black v → v ≠ root → m v ∈ Set.range (face v).corner)
    (hm_range : ∀ z, z ∉ Set.range (face root).corner ↔
      ∃ v, black v ∧ v ≠ root ∧ m v = z)
    (C : Barnette.CycleCoordinates D.graph)
    (hchoice : ∀ i, N.blackEndpoint black (D.cycleEdge C i) ≠ root ∧
      m (N.blackEndpoint black (D.cycleEdge C i)) = C.vertex i)
    (A : Finset V) (hroot : root ∉ A) (hcut : N.cut A = D.cycleEdges C) :
    (A.filter black).card + (N.cut A).card =
      (N.regionVertices D A).card + (N.blackCut black A).card := by
  let U := N.regionVertices D A
  let Z := D.cycleVertices C
  let B := A.filter black
  let M := B.image m
  let J := Finset.univ.filter fun i : Fin (C.n+3) =>
    N.blackEndpoint black (D.cycleEdge C i) ∈ A
  have face_region {v : V} (hv : v ∈ A) {z : F}
      (hz : z ∈ Set.range (face v).corner) : z ∈ U :=
    (N.regionVertices_iff_face D face A z).mpr ⟨v,hv,hz⟩
  have hZroot : ∀ z ∈ Z, z ∉ Set.range (face root).corner := by
    intro z hz
    obtain ⟨i,rfl⟩ := (D.mem_cycleVertices C z).mp hz
    apply (hm_range _).mpr
    exact ⟨_,(N.blackEndpoint_spec black hc _).1,(hchoice i).1,(hchoice i).2⟩
  have hZU : Z ⊆ U := by
    intro z hz
    obtain ⟨e,he,hez⟩ := (D.incident_cycle_iff C z).mpr hz
    rw [← hcut] at he
    refine (N.mem_regionVertices D A z).mpr ⟨e,?_,hez⟩
    rcases (N.mem_cut A e).mp he with ht | hh
    · exact (N.mem_regionEdges A e).mpr (Or.inl ht.1)
    · exact (N.mem_regionEdges A e).mpr (Or.inr hh.1)
  have hUroot : ∀ z ∈ U, z ∉ Set.range (face root).corner := by
    intro z hz hr
    have hzout : z ∈ N.regionVertices D Aᶜ :=
      (N.regionVertices_iff_face D face Aᶜ z).mpr ⟨root,Finset.mem_compl.mpr hroot,hr⟩
    have hh := N.mixed_corner_on_boundary D h sD face A hz hzout
    rw [hcut] at hh
    exact hZroot z ((D.incident_cycle_iff C z).mp hh) hr
  have hMU : M ⊆ U := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hvA,hvb⟩ := Finset.mem_filter.mp hv
    exact face_region hvA (hm_face v hvb (fun he => hroot (he ▸ hvA)))
  have h_union : M ∪ Z = U := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hMU hZU
    · intro z hz
      by_cases hzZ : z ∈ Z
      · exact Finset.mem_union_right _ hzZ
      obtain ⟨v,hvb,hvr,hvz⟩ := (hm_range z).mp (hUroot z hz)
      have hvA : v ∈ A := by
        by_contra hvA
        have hzout : z ∈ N.regionVertices D Aᶜ :=
          (N.regionVertices_iff_face D face Aᶜ z).mpr
            ⟨v,Finset.mem_compl.mpr hvA,hvz ▸ hm_face v hvb hvr⟩
        have hh := N.mixed_corner_on_boundary D h sD face A hz hzout
        rw [hcut] at hh
        exact hzZ ((D.incident_cycle_iff C z).mp hh)
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨v,Finset.mem_filter.mpr ⟨hvA,hvb⟩,hvz⟩)
  have h_inter : M ∩ Z = J.image C.vertex := by
    ext z
    constructor
    · rintro hz
      obtain ⟨hzM,hzZ⟩ := Finset.mem_inter.mp hz
      obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hzM
      obtain ⟨hvA,hvb⟩ := Finset.mem_filter.mp hv
      obtain ⟨i,hi⟩ := (D.mem_cycleVertices C z).mp hzZ
      have heq : v = N.blackEndpoint black (D.cycleEdge C i) :=
        hm_inj ⟨hvb,fun he => hroot (he ▸ hvA)⟩
          ⟨(N.blackEndpoint_spec black hc _).1,(hchoice i).1⟩
          (hvz.trans (hi.symm.trans (hchoice i).2.symm))
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq ▸ hvA⟩,hi⟩
    · rintro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      have hiA := (Finset.mem_filter.mp hi).2
      refine Finset.mem_inter.mpr ⟨?_,(D.mem_cycleVertices C _).mpr ⟨i,rfl⟩⟩
      exact Finset.mem_image.mpr ⟨_,Finset.mem_filter.mpr
        ⟨hiA,(N.blackEndpoint_spec black hc _).1⟩,(hchoice i).2⟩
  have hCJ : J.image (D.cycleEdge C) = N.blackCut black A := by
    ext e
    simp only [blackCut,Finset.mem_filter]
    constructor
    · intro he
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
      refine ⟨?_,(Finset.mem_filter.mp hi).2⟩
      rw [hcut]
      exact (D.mem_cycleEdges C _).mpr ⟨i,rfl⟩
    · rintro ⟨he,hb⟩
      rw [hcut] at he
      obtain ⟨i,rfl⟩ := (D.mem_cycleEdges C e).mp he
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩
  have hMcard : M.card = B.card := Finset.card_image_iff.mpr (by
    intro v hv w hw he
    obtain ⟨hvA,hvb⟩ := Finset.mem_filter.mp hv
    obtain ⟨hwA,hwb⟩ := Finset.mem_filter.mp hw
    exact hm_inj ⟨hvb,fun he => hroot (he ▸ hvA)⟩
      ⟨hwb,fun he => hroot (he ▸ hwA)⟩ he)
  have hZcard : Z.card = (N.cut A).card := by
    rw [hcut]
    simp only [Z,cycleVertices,cycleEdges,Finset.card_image_of_injective _ C.vertex.injective,
      Finset.card_image_of_injective _ (D.cycleEdge_injective C)]
  have hIcard : (M ∩ Z).card = (N.blackCut black A).card := by
    rw [h_inter,← hCJ]
    rw [Finset.card_image_of_injective _ C.vertex.injective,
      Finset.card_image_of_injective _ (D.cycleEdge_injective C)]
  have hh := Finset.card_union_add_card_inter M Z
  rw [h_union,hMcard,hZcard,hIcard] at hh
  exact hh.symm

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


theorem solution : type_of% @_root_.OAI.Barnette.Network.state_disk_count := @_root_.OAI.Barnette.Network.state_disk_count
