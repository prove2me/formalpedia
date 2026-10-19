-- Prove2me | solution 1 for OAI.Barnette.Network.independent_edges_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:33:41.867029+00:00
-- url     : https://prove2.me/submissions/24c987dc-a092-4063-876e-31abd4ca526f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Matching.lean:L188-L219
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.independent_edges_bound. The node keeps its source
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
theorem sum_boundary (x : E → ℝ) : ∑ v, N.boundary x v = 0 := by
  classical
  simp only [boundary_apply]
  rw [Finset.sum_comm]
  simp [Finset.sum_sub_distrib]

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

omit [Fintype E] in
lemma pull_push_injective {j : K → E} (hj : Function.Injective j) (x : K → ℝ) :
    pull j (push j x) = x := by
  classical
  ext k
  simp [hj.eq_iff]

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

lemma boundary_restrict_injective (hi : Function.Injective N.boundary)
    {K : Type*} [Fintype K] (j : K → E) (hj : Function.Injective j) :
    Function.Injective (N.restrict j).boundary := by
  intro x y h
  rw [boundary_restrict,boundary_restrict] at h
  have hh := congrArg (pull j) (hi h)
  simpa only [pull_push_injective hj] using hh

omit [Fintype V] [Fintype E] in
lemma boundary_supported_vertices {K : Type*} [Fintype K] (j : K → E)
    (U : Finset V) (hU : ∀ k, N.tail (j k) ∈ U ∧ N.head (j k) ∈ U)
    (x : K → ℝ) {v : V} (hv : v ∉ U) : (N.restrict j).boundary x v = 0 := by
  rw [boundary_apply]
  apply Finset.sum_eq_zero
  intro k _
  have ht : (N.restrict j).tail k ≠ v := fun hh => hv (hh ▸ (hU k).1)
  have hh : (N.restrict j).head k ≠ v := fun hh => hv (hh ▸ (hU k).2)
  simp [ht,hh]

lemma independent_edges_bound (hi : Function.Injective N.boundary)
    (S : Finset E) (U : Finset V) (hne : U.Nonempty)
    (hU : ∀ e ∈ S, N.tail e ∈ U ∧ N.head e ∈ U) : S.card + 1 ≤ U.card := by
  obtain ⟨v,hv⟩ := hne
  let H := N.restrict (Subtype.val : S → E)
  let L : (S → ℝ) →ₗ[ℝ] (U.erase v → ℝ) := (pull Subtype.val).comp H.boundary
  have hL : Function.Injective L := by
    intro x y hxy
    apply N.boundary_restrict_injective hi Subtype.val Subtype.val_injective
    have hrow : ∀ w, w ≠ v → H.boundary x w = H.boundary y w := by
      intro w hw
      by_cases hwU : w ∈ U
      · exact congrFun hxy ⟨w,Finset.mem_erase.mpr ⟨hw,hwU⟩⟩
      · rw [N.boundary_supported_vertices Subtype.val U (fun e => hU e.val e.property) x hwU,
          N.boundary_supported_vertices Subtype.val U (fun e => hU e.val e.property) y hwU]
    ext w
    by_cases hw : w = v
    · subst w
      have hsx := H.sum_boundary x
      have hsy := H.sum_boundary y
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)] at hsx hsy
      have hh : (∑ w ∈ Finset.univ.erase v, H.boundary x w) =
          ∑ w ∈ Finset.univ.erase v, H.boundary y w := by
        apply Finset.sum_congr rfl
        intro w hw; exact hrow w (Finset.mem_erase.mp hw).1
      linarith
    · exact hrow w hw
  have hc := LinearMap.finrank_le_finrank_of_injective hL
  simp only [Module.finrank_pi,Fintype.card_coe] at hc
  rw [Finset.card_erase_of_mem hv] at hc
  have hvp : 0 < U.card := Finset.card_pos.mpr ⟨v,hv⟩
  omega

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

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.independent_edges_bound := @_root_.OAI.Barnette.Network.independent_edges_bound
