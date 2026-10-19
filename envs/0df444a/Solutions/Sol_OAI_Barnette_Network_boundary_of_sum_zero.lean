-- Prove2me | solution 1 for OAI.Barnette.Network.boundary_of_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:51:01.054136+00:00
-- url     : https://prove2.me/submissions/59873979-e795-4726-be0a-1cf5b6ecf436

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Circulation.lean:L154-L181
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.boundary_of_sum_zero. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_Network_range_internal_boundary

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

lemma boundary_of_sum_zero (h : N.graph.Connected) (b : V → ℝ)
    (hb : ∑ v, b v = 0) : ∃ x, N.boundary x = b := by
  let q : V → Unit := fun _ => ()
  have hq : Function.Surjective q := by
    obtain ⟨v⟩ := h.nonempty
    intro u
    exact ⟨v,Subsingleton.elim _ _⟩
  have hg : (N.restrict (Subtype.val : N.internal q → E)).graph = N.graph := by
    ext v w
    constructor
    · rintro ⟨hne,e,he⟩
      exact ⟨hne,e.val,he⟩
    · rintro ⟨hne,e,he⟩
      exact ⟨hne,⟨e,rfl⟩,he⟩
  have hc : N.ConnectedFibers q := by
    intro v w _
    rw [hg]
    exact h v w
  have hz : push q b = 0 := by
    ext u
    cases u
    simpa [push,q] using hb
  have hm : b ∈ (N.restrict (Subtype.val : N.internal q → E)).boundary.range := by
    rw [N.range_internal_boundary hq hc]
    exact hz
  obtain ⟨x,hx⟩ := hm
  refine ⟨push (Subtype.val : N.internal q → E) x,?_⟩
  rw [← boundary_restrict,hx]

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.boundary_of_sum_zero := @_root_.OAI.Barnette.Network.boundary_of_sum_zero
