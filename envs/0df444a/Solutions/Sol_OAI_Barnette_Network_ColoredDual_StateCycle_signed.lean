-- Prove2me | solution 1 for OAI.Barnette.Network.ColoredDual.StateCycle.signed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:00:46.263602+00:00
-- url     : https://prove2.me/submissions/d2b03672-8d9a-4c24-90e0-258e00bfcb74

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/ColoredDual.lean:L183-L203
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.ColoredDual.StateCycle.signed. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_Triangle_index_delta
import Theorems.Thm_OAI_Barnette_Network_Triangle_potential_side
import Theorems.Thm_OAI_Barnette_Network_state_disk_delta
import Theorems.Thm_OAI_Barnette_Network_whiteCharge_cut_integral
import Theorems.Thm_OAI_Barnette_Network_white_positive_of_boundary

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
namespace OAI

/-! Cycle flows, minimal cuts, and connected shores. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

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

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

lemma whiteCharge_black (black : V → Prop) (root v : V)
    (hv : black v) (hvr : v ≠ root) : whiteCharge black root v = 0 := by
  simp [whiteCharge,hv,hvr]

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

end TriangleSystem
end Barnette
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma Triangle.oriented_cycleFlow (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) :
    D.cycleFlow (t.coordinates D) = N.gradient (fun w => if w = v then 1 else 0) := by
  ext e
  by_cases he : e ∈ N.star v
  · have hh : e ∈ Finset.univ.image t.edge := t.edge_range.symm ▸ he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hh
    have hflow := D.cycleFlow_apply_edge (t.coordinates D) i
    change D.cycleFlow (t.coordinates D) (D.cycleEdge (t.coordinates D) i) =
      D.arcSign (D.cycleEdge (t.coordinates D) i) (t.corner i) at hflow
    rw [t.coordinates_edge D sD i] at hflow
    exact hflow.trans (ht i).symm
  · have heC : e ∉ D.cycleEdges (t.coordinates D) := by
      rw [t.coordinates_edges D sD]; exact he
    rw [D.cycleFlow_zero_outside _ heC]
    have hy : e ∉ D.flowSupport (N.gradient (fun w => if w = v then 1 else 0)) := by
      rw [N.gradient_indicator_support D sN v]; exact he
    have hz : N.gradient (fun w => if w = v then 1 else 0) e = 0 := by
      simpa only [mem_flowSupport,not_not] using hy
    exact hz.symm

omit [Fintype V] [Fintype F] in
lemma cycle_integral (C : Barnette.CycleCoordinates D.graph) (α : E → ℝ) :
    ∑ e, α e * D.cycleFlow C e =
      ∑ i, α (D.cycleEdge C i) * D.arcSign (D.cycleEdge C i) (C.vertex i) := by
  simp only [cycleFlow,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [basisVec,mul_ite]

omit [Fintype F] in
lemma Triangle.oriented_integral (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) (α : E → ℝ) :
    ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = N.boundary α v := by
  have hh := D.cycle_integral (t.coordinates D) α
  rw [t.oriented_cycleFlow N D sN sD v ht] at hh
  have hb := N.boundary_adjoint α (fun w => if w = v then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hb
  rw [← hb] at hh
  have hf : D.cycleEdge (t.coordinates D) = t.edge := funext (t.coordinates_edge D sD)
  rw [hf] at hh
  exact hh.symm

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.side_unique (sD : D.Simple) {s : Finset E} (t : D.Triangle s)
    {i j : Fin 3} (hij : i ≠ j) {e : E}
    (he : s(D.tail e,D.head e) = s(t.corner i,t.corner j)) : e = t.side D i j :=
  sD.pair_injective (he.trans (t.side_ends D hij).symm)

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

omit [Fintype F] in
lemma weights_diff (root : V) (α : E → ℝ)
    (hα : N.boundary α = whiteCharge M.black root)
    (t : M.Black root) {i j : Fin 3} (hij : i ≠ j) :
    M.weights α root t j - M.weights α root t i =
      α ((M.face t.val).side D i j) *
        D.arcSign ((M.face t.val).side D i j) ((M.face t.val).corner i) := by
  apply (M.face t.val).potential_side D α _ hij
  rw [(M.face t.val).oriented_integral N D M.simple M.dual_simple t.val
    (M.oriented t.val) α,hα]
  exact whiteCharge_black M.black root t.val t.property.1 t.property.2

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

omit [Fintype F] in
lemma corner_ne (i : Fin (C.cycle.n+3)) : s.val (C.face i) ≠ C.corner i := by
  intro hh
  have hv : C.cycle.vertex i = C.cycle.vertex (i+1) :=
    (C.left_eq i).symm.trans ((congrArg (M.face (C.face i).val).corner hh).trans (C.right_eq i))
  exact (C.cycle.adjacent i).1 hv

omit [Fintype F] in
lemma cycleEdge_eq (i : Fin (C.cycle.n+3)) :
    D.cycleEdge C.cycle i = (M.face (C.face i).val).side D (s.val (C.face i)) (C.corner i) := by
  apply (M.face (C.face i).val).side_unique D M.dual_simple (C.corner_ne i)
  rw [D.cycleEdge_ends,C.right_eq]
  change s(C.cycle.vertex i,C.cycle.vertex (i+1)) =
    s(s.value (C.face i),C.cycle.vertex (i+1))
  rw [C.left_eq]

omit [Fintype F] in
lemma edge_mem (i : Fin (C.cycle.n+3)) : D.cycleEdge C.cycle i ∈ N.star (C.face i).val := by
  rw [C.cycleEdge_eq]
  exact (M.face (C.face i).val).side_mem D _ _

omit [Fintype F] in
lemma delta_eq : (C.delta : ℝ) = N.blackDelta D M.black C.cycle := by
  simp only [delta,Int.cast_sum,blackDelta]
  apply Finset.sum_congr rfl
  intro i _
  rw [(M.face (C.face i).val).index_delta N D (C.face i).val (M.oriented _)
    M.black M.coloring (C.face i).property.1 (C.corner_ne i),← C.cycleEdge_eq]
  change _ * D.arcSign _ (s.value (C.face i)) = _
  rw [C.left_eq]

omit [Fintype F] in
lemma slope_eq (α : E → ℝ) (hα : N.boundary α = whiteCharge M.black root) :
    C.slope α = ∑ e, α e * D.cycleFlow C.cycle e := by
  rw [D.cycle_integral]
  unfold slope
  apply Finset.sum_congr rfl
  intro i _
  rw [M.weights_diff root α hα (C.face i) (C.corner_ne i),← C.cycleEdge_eq]
  change _ * D.arcSign _ (s.value (C.face i)) = _
  rw [C.left_eq]

theorem signed (α : E → ℝ) (hα : N.boundary α = whiteCharge M.black root) :
    (C.delta = -3 ∧ 0 < C.slope α) ∨ (C.delta = 3 ∧ C.slope α < 0) := by
  obtain ⟨A,c,_ha,hr,hc,hflow,_hcut,hcount,hd⟩ :=
    M.cycle_disk s C.cycle C.face C.edge_mem C.left_eq
  have hδ : (C.delta : ℝ) = -3*c := C.delta_eq.trans hd
  have hs : C.slope α = c * ((A.filter fun v => ¬M.black v).card : ℝ) := by
    rw [C.slope_eq α hα]
    exact N.whiteCharge_cut_integral M.black root A hr α hα c _ hflow
  have hpos : (0:ℝ) < (A.filter fun v => ¬M.black v).card := by
    exact_mod_cast N.white_positive_of_boundary M.black M.coloring A hcount
  rcases hc with rfl | rfl
  · left
    constructor
    · have hh : (C.delta : ℝ) = (-3:ℝ) := by simpa using hδ
      exact_mod_cast hh
    · simpa [hs] using hpos
  · right
    constructor
    · have hh : (C.delta : ℝ) = (3:ℝ) := by simpa using hδ
      exact_mod_cast hh
    · simpa [hs] using neg_neg_of_pos hpos

end StateCycle
end
end Barnette.Network.ColoredDual

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network OAI.Barnette.Network.ColoredDual OAI.Barnette.Network.ColoredDual.StateCycle
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.ColoredDual.StateCycle.signed := @_root_.OAI.Barnette.Network.ColoredDual.StateCycle.signed
