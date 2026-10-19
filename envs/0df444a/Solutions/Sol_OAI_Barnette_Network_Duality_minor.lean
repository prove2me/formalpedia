-- Prove2me | solution 1 for OAI.Barnette.Network.Duality.minor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:55:40.540191+00:00
-- url     : https://prove2.me/submissions/3717bb05-f1e3-4fc8-9545-0ffd604e5808

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CappedDuality.lean:L62-L137
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.Duality.minor. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Theorems.Thm_OAI_Barnette_Network_connected_of_kernel_constants
import Theorems.Thm_OAI_Barnette_Network_range_internal_boundary

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

lemma push_pull_subtype (s : Set E) (x : E → ℝ) :
    push (Subtype.val : s → E) (pull Subtype.val x) = fun e => if e ∈ s then x e else 0 := by
  classical
  ext e
  by_cases he : e ∈ s
  · change (pull Subtype.val (push Subtype.val (pull Subtype.val x))) ⟨e, he⟩ = _
    rw [pull_push_injective Subtype.val_injective]
    simp [he]
  · rw [push_eq_zero_outside _ (by simpa using he)]
    simp [he]

end
end Barnette.Network

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

end TriangleSystem.Pair
end
end Barnette
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
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {F : Type*} [Fintype F]
omit [Fintype E] [Fintype F] in
lemma componentMap_surjective (H : Network F E) : Function.Surjective H.componentMap := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h f => exact ⟨f, rfl⟩

omit [Fintype E] [Fintype F] in
lemma gradient_componentMap (H : Network F E) (f : H.Components → ℝ) :
    H.gradient (pull H.componentMap f) = 0 := by
  apply (H.gradient_eq_zero_iff _).mpr
  intro e
  exact congrArg f (SimpleGraph.ConnectedComponent.sound (H.edge_reachable e)).symm

omit [Fintype E] [Fintype F] in
lemma descends_components (H : Network F E) (g : F → ℝ) (hg : H.gradient g = 0) :
    ∃ f : H.Components → ℝ, pull H.componentMap f = g := by
  refine ⟨Quot.lift g (fun v w h => H.gradient_zero_reachable hg h), ?_⟩
  rfl

end
end Barnette.Network

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
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network
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
lemma boundary_range_restrict (s : Set E) :
    (N.restrict (Subtype.val : s → E)).boundary.range =
      Submodule.span ℝ (N.incidence.col '' s) := by
  let : DecidableEq s := Classical.decEq _
  rw [boundary, Matrix.range_toLin']
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.val, e.property, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩

omit [Fintype V] in

lemma exists_independent_restriction (s : Set E) :
    ∃ r ⊆ s,
      Function.Injective (N.restrict (Subtype.val : r → E)).boundary ∧
      (N.restrict (Subtype.val : r → E)).boundary.range =
        (N.restrict (Subtype.val : s → E)).boundary.range := by
  obtain ⟨r, hrs, _, hspan, hi⟩ := exists_linearIndepOn_extension
    (v := N.incidence.col) (linearIndepOn_empty ℝ _) (Set.empty_subset s)
  refine ⟨r, hrs, ?_, ?_⟩
  · exact Matrix.mulVec_injective_iff.mpr hi
  · rw [N.boundary_range_restrict, N.boundary_range_restrict]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hrs)
    · exact Submodule.span_le.mpr hspan

variable {F : Type*} [Fintype F] (D : Network F E)

lemma duality_of_first_exact (hN : N.graph.Connected) (hD : D.graph.Connected)
    (he : N.boundary.ker = D.gradient.range) : N.Duality D := by
  have ho : ∀ f, N.boundary (D.gradient f) = 0 := by
    intro f
    change D.gradient f ∈ N.boundary.ker
    rw [he]
    exact ⟨f, rfl⟩
  have h₁ := N.dim_cycles hN
  rw [he] at h₁
  have h₂ := D.rank_gradient hD
  exact N.duality_of_orth_card D hN hD (by omega) ho

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

omit [Fintype E] in
lemma push_pull_injective {j : K → E} (hj : Function.Injective j) (x : E → ℝ) :
    push j (pull j x) = fun e => if e ∈ Set.range j then x e else 0 := by
  ext e
  by_cases he : e ∈ Set.range j
  · obtain ⟨k, rfl⟩ := he
    have h := congrFun (pull_push_injective hj (pull j x)) k
    simpa only [pull_apply, Set.mem_range_self, ite_true] using h
  · rw [push_eq_zero_outside _ he]
    simp only [he, ite_false]

omit [Fintype K] in
lemma pull_push_disjoint {j : K → E} (r : Set E)
    (hr : ∀ k, j k ∉ r) (x : r → ℝ) :
    pull j (push (Subtype.val : r → E) x) = 0 := by
  ext k
  exact push_eq_zero_outside x (by simpa using hr k)

lemma split_support {j : K → E} (hj : Function.Injective j) (r : Set E)
    (hr : ∀ k, j k ∉ r) (x : E → ℝ)
    (hx : ∀ e, e ∉ r → e ∉ Set.range j → x e = 0) :
    x = push j (pull j x) + push (Subtype.val : r → E) (pull Subtype.val x) := by
  rw [push_pull_injective hj, push_pull_subtype]
  ext e
  by_cases he : e ∈ r
  · have hj' : e ∉ Set.range j := by
      rintro ⟨k, rfl⟩
      exact hr k he
    simp only [Pi.add_apply, he, hj', ite_true, ite_false, zero_add]
  · by_cases hj' : e ∈ Set.range j
    · simp only [Pi.add_apply, he, hj', ite_true, ite_false, add_zero]
    · simp only [Pi.add_apply, he, hj', ite_false, hx e he hj', zero_add]

lemma push_boundary_on_internal (N : Network V E) (q : V → W) (r : Set E)
    (hr : r ⊆ N.internal q) (x : r → ℝ) :
    push q ((N.restrict Subtype.val).boundary x) = 0 := by
  apply eq_of_dot_eq
  intro f
  rw [push_adjoint, (N.restrict _).boundary_adjoint]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro e _
  have he : (N.restrict (Subtype.val : r → E)).gradient (pull q f) e = 0 := by
    change f (q (N.head e.val)) - f (q (N.tail e.val)) = 0
    rw [show q (N.tail e.val) = q (N.head e.val) from hr e.property]
    exact sub_self _
  rw [he, mul_zero]

theorem Duality.minor (N : Network V E) (D : Network F E) (h : N.Duality D)
    (q : V → W) (hq : Function.Surjective q) (hc : N.ConnectedFibers q)
    (j : K → E) (hj : Function.Injective j)
    (hjext : ∀ k, q (N.tail (j k)) ≠ q (N.head (j k)))
    (hM : ((N.mapVertices q).restrict j).graph.Connected) :
    ∃ (L : Type uF) (_ : Fintype L) (dual : Network L K),
      ((N.mapVertices q).restrict j).Duality dual := by
  obtain ⟨r, hr, hir, her⟩ := N.exists_independent_restriction (N.internal q)
  have hrj : ∀ k, j k ∉ r := fun k hk => hjext k (hr hk)
  let d : Set E := {e | e ∉ r ∧ e ∉ Set.range j}
  let H := D.restrict (Subtype.val : d → E)
  let qD := H.componentMap
  let L := (D.mapVertices qD).restrict j
  let M := (N.mapVertices q).restrict j
  have hqD : Function.Surjective qD := H.componentMap_surjective
  have zeroD (f : H.Components → ℝ) (e : E) (he : e ∈ d) :
      D.gradient (pull qD f) e = 0 := congrFun (H.gradient_componentMap f) ⟨e, he⟩
  have orth (f : F → ℝ) : N.boundary (D.gradient f) = 0 := by
    change D.gradient f ∈ N.boundary.ker
    rw [h.cycles_eq_cuts]
    exact ⟨f, rfl⟩
  have hle : L.gradient.range ≤ M.boundary.ker := by
    rintro _ ⟨f, rfl⟩
    have hs := split_support hj r hrj (D.gradient (pull qD f))
      (fun e he hej => zeroD f e ⟨he, hej⟩)
    have hz := congrArg (push q) (orth (pull qD f))
    rw [hs, map_add, map_add, map_zero,
      ← boundary_restrict, ← boundary_restrict,
      push_boundary_on_internal N q r hr, add_zero] at hz
    change M.boundary (L.gradient f) = 0
    rw [boundary_restrict, boundary_mapVertices]
    simpa only [boundary_restrict, L, gradient_restrict, gradient_mapVertices] using hz
  have hge : M.boundary.ker ≤ L.gradient.range := by
    intro x hx
    have hz : push q (N.boundary (push j x)) = 0 := by
      have he : M.boundary x = 0 := hx
      simpa only [M, boundary_restrict, boundary_mapVertices] using he
    have hy : N.boundary (push j x) ∈ (N.restrict (Subtype.val : r → E)).boundary.range := by
      rw [her, N.range_internal_boundary hq hc]
      exact hz
    obtain ⟨y, hy⟩ := hy
    let z := push j x - push (Subtype.val : r → E) y
    have hzb : N.boundary z = 0 := by
      rw [map_sub, ← N.boundary_restrict (Subtype.val : r → E) y, hy, sub_self]
    have hzg : z ∈ D.gradient.range := by rw [← h.cycles_eq_cuts]; exact hzb
    obtain ⟨g, hg⟩ := hzg
    have hgH : H.gradient g = 0 := by
      ext e
      change D.gradient g e.val = 0
      rw [hg]
      have he : e.val ∉ Set.range (Subtype.val : r → E) := by simpa using e.property.1
      simp only [z, Pi.sub_apply, push_eq_zero_outside x e.property.2,
        push_eq_zero_outside y he, sub_self]
    obtain ⟨f, hf⟩ := H.descends_components g hgH
    refine ⟨f, ?_⟩
    change pull j (D.gradient (pull qD f)) = x
    rw [hf, hg, map_sub, pull_push_injective hj, pull_push_disjoint r hrj, sub_zero]
  have hLc : L.graph.Connected := by
    have : Nonempty F := h.dual_connected.nonempty
    have : Nonempty H.Components := Nonempty.map qD inferInstance
    apply L.connected_of_kernel_constants
    intro f hf a b
    have hs := split_support hj r hrj (D.gradient (pull qD f))
      (fun e he hej => zeroD f e ⟨he, hej⟩)
    have hjzero : pull j (D.gradient (pull qD f)) = 0 := hf
    rw [hjzero, map_zero, zero_add] at hs
    have hz := orth (pull qD f)
    rw [hs, ← boundary_restrict] at hz
    have hrzero : pull (Subtype.val : r → E) (D.gradient (pull qD f)) = 0 := by
      apply hir
      simpa only [map_zero] using hz
    rw [hrzero, map_zero] at hs
    obtain ⟨a', rfl⟩ := hqD a
    obtain ⟨b', rfl⟩ := hqD b
    exact D.gradient_zero_reachable hs (h.dual_connected a' b')
  exact ⟨H.Components, inferInstance, L, M.duality_of_first_exact L hM hLc (le_antisymm hge hle)⟩

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
universe uF
variable {V E : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network
namespace Barnette.SimpleCycle
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

end
end Barnette.SimpleCycle

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution.{uF,u_1,u_2,u_3,u_4} : type_of% @_root_.OAI.Barnette.Network.Duality.minor.{uF,u_1,u_2,u_3,u_4} := @_root_.OAI.Barnette.Network.Duality.minor.{uF,u_1,u_2,u_3,u_4}
