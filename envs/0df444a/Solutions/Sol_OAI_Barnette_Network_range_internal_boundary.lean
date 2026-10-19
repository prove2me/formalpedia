-- Prove2me | solution 1 for OAI.Barnette.Network.range_internal_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:34:07.581491+00:00
-- url     : https://prove2.me/submissions/a9e150e7-27bb-43e6-a0f0-056a8ffc8887

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Quotients.lean:L169-L190
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.range_internal_boundary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients

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
omit [Fintype E] in
theorem gradient_matrix : N.gradient = Matrix.toLin' N.incidence.transpose := by
  classical
  apply LinearMap.ext
  intro f
  ext e
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, incidence,
    sub_mul, ite_mul, Finset.sum_sub_distrib]

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

lemma push_surjective {q : V → W} (hq : Function.Surjective q) :
    Function.Surjective (push q) := by
  classical
  let r := Function.surjInv hq
  have hr : Function.RightInverse r q := Function.rightInverse_surjInv hq
  intro f
  refine ⟨fun v => if h : v ∈ Set.range r then f (q v) else 0, ?_⟩
  ext w
  simp only [push_apply]
  rw [Finset.sum_eq_single (r w)]
  · simp [hr w]
  · intro v _ hv
    by_cases h : v ∈ Set.range r
    · obtain ⟨z, rfl⟩ := h
      have hz : z ≠ w := fun he => hv (congrArg r he)
      simp [hr z, hz]
    · simp [h]
  · simp

omit [Fintype V] [Fintype W] in
lemma pull_injective {q : V → W} (hq : Function.Surjective q) :
    Function.Injective (pull q) := by
  intro f g h
  ext w
  obtain ⟨v, rfl⟩ := hq w
  exact congrFun h v

lemma eq_of_dot_eq (x y : V → ℝ)
    (h : ∀ f : V → ℝ, ∑ v, x v * f v = ∑ v, y v * f v) : x = y := by
  ext v
  have hh := h (fun w => if w = v then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using hh

lemma push_boundary_internal (N : Network V E) (q : V → W)
    (x : N.internal q → ℝ) :
    push q ((N.restrict Subtype.val).boundary x) = 0 := by
  apply eq_of_dot_eq
  intro f
  rw [push_adjoint, (N.restrict _).boundary_adjoint]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro e _
  have he : (N.restrict (Subtype.val : N.internal q → E)).gradient (pull q f) e = 0 := by
    change f (q (N.head e.val)) - f (q (N.tail e.val)) = 0
    rw [e.property]
    exact sub_self _
  rw [he, mul_zero]

omit [Fintype V] [Fintype W] [Fintype E] in
lemma ker_internal_gradient (N : Network V E) {q : V → W}
    (hq : Function.Surjective q) (hc : N.ConnectedFibers q) :
    (N.restrict (Subtype.val : N.internal q → E)).gradient.ker = (pull q).range := by
  classical
  ext f
  constructor
  · intro hf
    let r := Function.surjInv hq
    have hr := Function.rightInverse_surjInv hq
    refine ⟨fun w => f (r w), ?_⟩
    ext v
    exact (N.restrict _).gradient_zero_reachable hf (hc _ _ (hr (q v)))
  · rintro ⟨f, rfl⟩
    apply (N.restrict _).gradient_eq_zero_iff _ |>.mpr
    intro e
    exact congrArg f e.property.symm

lemma range_internal_boundary (N : Network V E) {q : V → W}
    (hq : Function.Surjective q) (hc : N.ConnectedFibers q) :
    (N.restrict (Subtype.val : N.internal q → E)).boundary.range = (push q).ker := by
  classical
  let : DecidableEq (N.internal q) := Classical.decEq _
  let I := N.restrict (Subtype.val : N.internal q → E)
  have hle : I.boundary.range ≤ (push q).ker := by
    rintro _ ⟨x, rfl⟩
    exact N.push_boundary_internal q x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hk : Module.finrank ℝ I.gradient.ker = Fintype.card W := by
    rw [show I.gradient.ker = (pull q).range from N.ker_internal_gradient hq hc,
      LinearMap.finrank_range_of_inj (pull_injective hq), Module.finrank_pi]
  have hgrad := I.gradient.finrank_range_add_finrank_ker
  have hpush := (push q).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (push_surjective hq), finrank_top,
    Module.finrank_pi, Module.finrank_pi] at hpush
  have hr : Module.finrank ℝ I.boundary.range = Module.finrank ℝ I.gradient.range := by
    rw [I.gradient_matrix, boundary, Matrix.toLin'_apply', Matrix.toLin'_apply',
      ← Matrix.rank, ← Matrix.rank, Matrix.rank_transpose]
  rw [Module.finrank_pi, hk] at hgrad
  omega

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.range_internal_boundary := @_root_.OAI.Barnette.Network.range_internal_boundary
