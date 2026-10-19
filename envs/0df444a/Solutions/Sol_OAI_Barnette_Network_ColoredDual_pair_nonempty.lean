-- Prove2me | solution 1 for OAI.Barnette.Network.ColoredDual.pair_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:29:26.75291+00:00
-- url     : https://prove2.me/submissions/9f3bef6a-4e82-4338-b3d5-0f0f571026e0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/BMatching.lean:L403-L427
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.ColoredDual.pair_nonempty. The node keeps its source
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
import Theorems.Thm_OAI_Barnette_BMatching_data_of_gadget
import Theorems.Thm_OAI_Barnette_BMatching_gadget_hall
import Theorems.Thm_OAI_Barnette_Network_Triangle_all_corners
import Theorems.Thm_OAI_Barnette_Network_black_dual_card
import Theorems.Thm_OAI_Barnette_Network_black_edge_partition
import Theorems.Thm_OAI_Barnette_Network_card_star
import Theorems.Thm_OAI_Barnette_Network_complement_singleton_root
import Theorems.Thm_OAI_Barnette_Network_connected_of_kernel_constants
import Theorems.Thm_OAI_Barnette_Network_region_balance_rim
import Theorems.Thm_OAI_Barnette_Network_rim_cut_count
import Theorems.Thm_OAI_Barnette_Network_rim_three_cut

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

-- ---- from OAI.Combinatorics.Hamiltonian.Contraction ----
namespace OAI

/-! Contraction and deletion of finite oriented dual networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma inducedNetwork_map (U : Finset F) :
    (D.inducedNetwork U).mapVertices Subtype.val =
      D.restrict (Subtype.val : D.inducedEdges U → E) := rfl

lemma inducedNetwork_boundary (U : Finset F) (x : D.inducedEdges U → ℝ) :
    push (Subtype.val : U → F) ((D.inducedNetwork U).boundary x) =
      D.boundary (push Subtype.val x) := by
  rw [← boundary_mapVertices,D.inducedNetwork_map,boundary_restrict]

omit [Fintype V] [Fintype F] in
lemma regionQuotient_connected (hN : N.graph.Connected) (U : Finset F) :
    (N.regionQuotient D U).graph.Connected := by
  let H := N.regions D U
  let q := H.componentMap
  let L := N.regionQuotient D U
  have : Nonempty V := hN.nonempty
  have : Nonempty H.Components := Nonempty.map q inferInstance
  apply L.connected_of_kernel_constants
  intro f hf a b
  obtain ⟨a',rfl⟩ := H.componentMap_surjective a
  obtain ⟨b',rfl⟩ := H.componentMap_surjective b
  apply N.gradient_zero_reachable (f := pull q f) _ (hN a' b')
  ext e
  by_cases he : e ∈ D.inducedEdges U
  · exact congrFun hf ⟨e,he⟩
  · exact congrFun (H.gradient_componentMap f) ⟨e,he⟩

omit [Fintype V] in

lemma induced_cycles_eq_regions (h : N.Duality D) (U : Finset F) :
    (D.inducedNetwork U).boundary.ker = (N.regionQuotient D U).gradient.range := by
  let H := N.regions D U
  let q := H.componentMap
  ext x
  constructor
  · intro hx
    have hx' : (D.inducedNetwork U).boundary x = 0 := hx
    have hz : D.boundary (push (Subtype.val : D.inducedEdges U → E) x) = 0 := by
      rw [← D.inducedNetwork_boundary,hx',map_zero]
    obtain ⟨g,hg⟩ : ∃ g, N.gradient g = push (Subtype.val : D.inducedEdges U → E) x := by
      have hh : push (Subtype.val : D.inducedEdges U → E) x ∈ D.boundary.ker := hz
      rw [h.dual_cycles_eq_cuts] at hh
      exact hh
    have hgH : H.gradient g = 0 := by
      ext e
      change N.gradient g e.val = 0
      rw [hg]
      exact push_eq_zero_outside x (by simpa using e.property)
    obtain ⟨f,hf⟩ := H.descends_components g hgH
    refine ⟨f,?_⟩
    change pull (Subtype.val : D.inducedEdges U → E) (N.gradient (pull q f)) = x
    rw [hf,hg,pull_push_injective Subtype.val_injective]
  · rintro ⟨f,rfl⟩
    have hext : push (Subtype.val : D.inducedEdges U → E)
        ((N.regionQuotient D U).gradient f) = N.gradient (pull q f) := by
      ext e
      by_cases he : e ∈ D.inducedEdges U
      · exact push_subtype_apply (D.inducedEdges U) _ ⟨e,he⟩
      · rw [push_eq_zero_outside _ (by simpa using he)]
        exact (congrFun (H.gradient_componentMap f) ⟨e,he⟩).symm
    have hz : push (Subtype.val : U → F)
        ((D.inducedNetwork U).boundary ((N.regionQuotient D U).gradient f)) = 0 := by
      rw [D.inducedNetwork_boundary,hext]
      exact h.dual_conserved_gradient N D _
    have hz' := congrArg (pull (Subtype.val : U → F)) hz
    rw [pull_push_injective Subtype.val_injective,map_zero] at hz'
    exact hz'

omit [Fintype F] in
lemma rank_boundary_le [Nonempty V] :
    Module.finrank ℝ N.boundary.range + 1 ≤ Fintype.card V := by
  have hle : (constant (V := V)).range ≤ N.gradient.ker := by
    rintro _ ⟨c,rfl⟩
    exact N.gradient_const c
  have hi : Function.Injective (constant (V := V)) := by
    intro a b hh
    exact congrFun hh (Classical.choice inferInstance)
  have hk : 1 ≤ Module.finrank ℝ N.gradient.ker := by
    have hh := Submodule.finrank_mono hle
    rwa [LinearMap.finrank_range_of_inj hi,Module.finrank_self] at hh
  have hr : Module.finrank ℝ N.boundary.range = Module.finrank ℝ N.gradient.range := by
    rw [N.gradient_matrix,boundary,Matrix.toLin'_apply',Matrix.toLin'_apply',
      ← Matrix.rank,← Matrix.rank,Matrix.rank_transpose]
  have hh := N.gradient.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hh
  omega

lemma induced_euler_bound (h : N.Duality D) (U : Finset F) (hU : U.Nonempty) :
    (D.inducedEdges U).card + 2 ≤ U.card + Fintype.card (N.Regions D U) := by
  have : Nonempty U := by obtain ⟨u,hu⟩ := hU; exact ⟨⟨u,hu⟩⟩
  have hr := (D.inducedNetwork U).rank_boundary_le
  have hk := (D.inducedNetwork U).boundary.finrank_range_add_finrank_ker
  rw [Module.finrank_pi,Fintype.card_coe] at hk
  rw [N.induced_cycles_eq_regions D h U] at hk
  have ho := (N.regionQuotient D U).rank_gradient (N.regionQuotient_connected D h.connected U)
  simp only [Fintype.card_coe] at hr
  omega

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
lemma star_count (hN : N.Simple) (v : V) :
    (N.star v).card = ∑ e, ((if N.tail e = v then 1 else 0) +
      (if N.head e = v then 1 else 0)) := by
  rw [star,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hne := hN.loopless e
  by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all [Incident]

lemma weighted_stars (hN : N.Simple) (f : V → ℤ) :
    ∑ v, f v * (N.star v).card = ∑ e, (f (N.tail e) + f (N.head e)) := by
  simp only [N.star_count hN,Nat.cast_sum,Nat.cast_add,Nat.cast_ite,Nat.cast_one,
    Nat.cast_zero,Finset.mul_sum,mul_add,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [Finset.sum_add_distrib,eq_comm]

omit [Fintype V] [Fintype E] in
lemma colorSign_add (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    colorSign black (N.tail e) + colorSign black (N.head e) = 0 := by
  have he := hc e
  by_cases ht : black (N.tail e) <;> by_cases hh : black (N.head e) <;>
    simp_all [colorSign]

lemma colorSign_sum (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    ∑ v, colorSign black v = 0 := by
  have hs := N.weighted_stars hN (colorSign black)
  have hv : ∀ v, (N.star v).card = 3 := fun v => (N.card_star hN v).trans (h3 v)
  simp only [hv,N.colorSign_add black hc,Finset.sum_const_zero,Nat.cast_ofNat,
    ← Finset.sum_mul] at hs
  omega

omit [Fintype F] in
lemma regionShore_nonempty (U : Finset F) (q : N.Regions D U) :
    (N.regionShore D U q).Nonempty := by
  obtain ⟨v,hv⟩ := (N.regions D U).componentMap_surjective q
  exact ⟨v,(N.mem_regionShore D U q v).mpr hv⟩

omit [Fintype F] in
lemma regionShore_off_edge (U : Finset F) (q : N.Regions D U) {e : E}
    (he : e ∉ D.inducedEdges U) :
    N.tail e ∈ N.regionShore D U q ↔ N.head e ∈ N.regionShore D U q := by
  simp only [N.mem_regionShore]
  have hh : (N.regions D U).componentMap (N.tail e) =
      (N.regions D U).componentMap (N.head e) :=
    SimpleGraph.ConnectedComponent.sound ((N.regions D U).edge_reachable ⟨e,he⟩)
  rw [hh]

omit [Fintype F] in
lemma blackRim_le (black : V → Prop) (U : Finset F) (q : N.Regions D U) :
    N.blackRim D black U q ≤ N.rim D U q := by
  apply Finset.sum_le_sum
  intro e _
  by_cases ht : N.tail e ∈ N.regionShore D U q <;>
    by_cases hh : N.head e ∈ N.regionShore D U q <;>
    by_cases bt : black (N.tail e) <;> by_cases bh : black (N.head e) <;> simp [ht,hh,bt,bh]

omit [Fintype F] in
lemma sum_rim (U : Finset F) :
    ∑ q : N.Regions D U, N.rim D U q = 2 * (D.inducedEdges U).card := by
  simp only [rim]
  rw [Finset.sum_comm]
  simp [N.mem_regionShore,Finset.sum_add_distrib,Nat.mul_comm]

omit [Fintype F] in
lemma sum_regionBalance (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) : ∑ q : N.Regions D U, N.regionBalance D black U q = 0 := by
  simp only [regionBalance,regionShore,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact N.colorSign_sum hN h3 black hc

lemma rim_defect (b d : ℕ) (β : ℤ) (hb : b ≤ d) (hd : 4 ≤ d)
    (hβ : 3*β = 2*(b:ℤ) - d) : β ≤ (d:ℤ)-4 := by
  by_cases h4 : d = 4
  · subst d; omega
  by_cases h5 : d = 5
  · subst d; omega
  have h6 : (6:ℤ) ≤ d := by omega
  have hbd : (b:ℤ) ≤ d := by exact_mod_cast hb
  omega

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma cut_le_rim (U : Finset F) (q : N.Regions D U) :
    (N.cut (N.regionShore D U q)).card ≤ N.rim D U q := by
  rw [N.rim_cut_count]
  omega

omit [Fintype F] in
lemma rim_of_shore_univ (U : Finset F) (q : N.Regions D U)
    (hq : N.regionShore D U q = Finset.univ) :
    N.rim D U q = 2 * (D.inducedEdges U).card := by
  simp [rim,hq,Nat.mul_comm]

omit [Fintype F] in
lemma rim_ge_three (hN : N.ThreeEdgeConnected) (U : Finset F)
    (hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) : 3 ≤ N.rim D U q := by
  by_cases hq : N.regionShore D U q = Finset.univ
  · rw [N.rim_of_shore_univ D U q hq]; omega
  · have hA := N.regionShore_nonempty D U q
    have hAc : (N.regionShore D U q)ᶜ.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      exact hq ((Finset.compl_eq_empty_iff _).mp he)
    exact (hN _ hA hAc).trans (N.cut_le_rim D U q)

omit [Fintype F] in
lemma singleton_region_star (hN : N.Simple) (U : Finset F) (q : N.Regions D U)
    {v : V} (hq : N.regionShore D U q = {v}) : N.star v ⊆ D.inducedEdges U := by
  intro e he
  by_contra hn
  have hi := (N.mem_star e v).mp he
  have hh := N.regionShore_off_edge D U q hn
  rw [hq] at hh
  simp only [Finset.mem_singleton] at hh
  exact hN.loopless e (hi.elim (fun hv => hv.trans ((hh.mp hv).symm))
    (fun hv => (hh.mpr hv).trans hv.symm))

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.MinorDuality ----
namespace OAI

/-! Exact duality under finite network minors. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma sum_regionBlack (black : V → Prop) (U : Finset F) :
    ∑ q : N.Regions D U, N.regionBlack D black U q = (N.fullBlack D black U).card := by
  simp only [regionBlack,Finset.card_filter,N.mem_regionShore]
  rw [Finset.sum_comm]
  simp

omit [Fintype F] in
lemma regionBalance_singleton (black : V → Prop) (U : Finset F) (q : N.Regions D U)
    {v : V} (hq : N.regionShore D U q = {v}) :
    N.regionBalance D black U q = colorSign black v := by
  simp [regionBalance,hq]

omit [Fintype F] in
lemma regionBalance_complement_singleton (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) (q : N.Regions D U) {v : V} (hq : (N.regionShore D U q)ᶜ = {v}) :
    N.regionBalance D black U q = -colorSign black v := by
  have hh := Finset.sum_add_sum_compl (N.regionShore D U q) (colorSign black)
  rw [N.colorSign_sum hN h3 black hc,hq,Finset.sum_singleton] at hh
  change (∑ v ∈ N.regionShore D U q, colorSign black v) = _
  omega

omit [Fintype F] in
lemma singleton_regionBlack (hN : N.Simple) (black : V → Prop)
    (U : Finset F) (q : N.Regions D U) {v : V}
    (hq : N.regionShore D U q = {v}) (hv : black v) :
    1 ≤ N.regionBlack D black U q := by
  apply Finset.card_pos.mpr
  refine ⟨v,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
  · simp only [fullBlack,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨hv,N.singleton_region_star D hN U q hq⟩
  · simp [hq]

omit [Fintype F] in

lemma region_density (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (root : V) (hbroot : black root) (U : Finset F)
    (hr : N.star root ⊆ D.inducedEdges U) (q : N.Regions D U) :
    4 + N.regionBalance D black U q - 2*(N.regionBlack D black U q : ℤ) ≤ N.rim D U q := by
  have hm : 3 ≤ (D.inducedEdges U).card := by
    have hh := Finset.card_le_card hr
    rwa [N.card_star hN,h3 root] at hh
  have hd := N.rim_ge_three D hcut U hm q
  by_cases hd4 : 4 ≤ N.rim D U q
  · have hh := rim_defect (N.blackRim D black U q) (N.rim D U q)
      (N.regionBalance D black U q) (N.blackRim_le D black U q) hd4
      (N.region_balance_rim D hN h3 black hc U q)
    omega
  · have hd3 : N.rim D U q = 3 := by omega
    rcases htr _ (N.rim_three_cut D hcut U hm q hd3) with hsing | hsing
    · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hsing
      have hβ := N.regionBalance_singleton D black U q hv
      by_cases hb : black v
      · have hB := N.singleton_regionBlack D hN black U q hv hb
        simp only [colorSign,hb,ite_true] at hβ
        omega
      · simp only [colorSign,hb,ite_false] at hβ
        omega
    · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hsing
      have hvr := N.complement_singleton_root D hN h3 hcut U root hr q hd3 hv
      have hβ := N.regionBalance_complement_singleton D hN h3 black hc U q hv
      rw [hvr] at hβ
      simp only [colorSign,hbroot,ite_true] at hβ
      omega

theorem induced_density (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (root : V) (hbroot : black root) (U : Finset F)
    (hr : N.star root ⊆ D.inducedEdges U) :
    ((D.inducedEdges U).card : ℤ) - (N.fullBlack D black U).card ≤ 2*(U.card : ℤ)-4 := by
  have hU : U.Nonempty := by
    have hstar : (N.star root).Nonempty := Finset.card_pos.mp (by rw [N.card_star hN,h3 root]; decide)
    obtain ⟨e,he⟩ := hstar
    exact ⟨D.tail e,((D.mem_inducedEdges U e).mp (hr he)).1⟩
  have heuler := N.induced_euler_bound D h U hU
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun q _ => N.region_density D hN h3 hcut htr black hc root hbroot U hr q)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,← Nat.cast_sum,
    N.sum_regionBalance D hN h3 black hc,N.sum_regionBlack,N.sum_rim] at hsum
  push_cast at hsum
  omega

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma three_corner_count (p : Fin 3 → Prop) :
    ((min (2 : ℕ) ((Finset.univ.filter fun i => ¬p i).card) : ℕ) : ℤ) +
      (∑ i : Fin 3, if p i ∧ p (i+1) then (1 : ℤ) else 0) =
        2 + if ∀ i, p i then 1 else 0 := by
  have h11 : (1 : Fin 3) + 1 = 2 := by decide
  have h21 : (2 : Fin 3) + 1 = 0 := by decide
  by_cases h0 : p 0 <;> by_cases h1 : p 1 <;> by_cases h2 : p 2 <;>
    simp only [Finset.card_filter,Fin.sum_univ_succ,Fin.forall_fin_succ] <;>
    norm_num [h0,h1,h2,h11,h21]

omit [Fintype V] [Fintype F] in
lemma Triangle.edges_in_count {s : Finset E} (t : D.Triangle s) (U : Finset F) :
    ((s.filter fun e => e ∈ D.inducedEdges U).card : ℤ) =
      ∑ i : Fin 3, if t.corner i ∈ U ∧ t.corner (i+1) ∈ U then (1 : ℤ) else 0 := by
  conv_lhs => rw [← t.edge_range]
  rw [Finset.filter_image,Finset.card_image_of_injective _ t.edge_injective,
    Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := t.edge_ends i
  have hh : t.edge i ∈ D.inducedEdges U ↔ t.corner i ∈ U ∧ t.corner (i+1) ∈ U := by
    rw [D.mem_inducedEdges]
    rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩ <;> simp [ht,hh,and_comm]
  simp [hh]

omit [Fintype F] in
lemma capacity_identity (face : ∀ v, D.Triangle (N.star v))
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (U : Finset F) :
    (∑ v ∈ Finset.univ.filter black,
      ((min (2 : ℕ) ((Finset.univ.filter fun i => (face v).corner i ∉ U).card) : ℕ) : ℤ)) +
        (D.inducedEdges U).card =
      2 * ((Finset.univ.filter black).card : ℤ) + (N.fullBlack D black U).card := by
  have he := N.black_edge_partition black hc (D.inducedEdges U)
  have hb : (∑ v ∈ Finset.univ.filter black,
      if N.star v ⊆ D.inducedEdges U then (1 : ℤ) else 0) = (N.fullBlack D black U).card := by
    simp only [fullBlack,Finset.card_filter,Nat.cast_sum,Finset.sum_filter,
      ite_and,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  calc
    _ = ∑ v ∈ Finset.univ.filter black,
        (((min (2 : ℕ) ((Finset.univ.filter fun i => (face v).corner i ∉ U).card) : ℕ) : ℤ) +
        ((N.star v).filter fun e => e ∈ D.inducedEdges U).card) := by
      simp only [Finset.sum_add_distrib,← Nat.cast_sum,he]
    _ = ∑ v ∈ Finset.univ.filter black,
        (2 + if N.star v ⊆ D.inducedEdges U then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [(face v).edges_in_count D U]
      simp only [(face v).all_corners D U]
      convert three_corner_count (fun i => (face v).corner i ∈ U) using 1 <;> congr!
    _ = _ := by rw [Finset.sum_add_distrib,hb]; simp [mul_comm]

theorem capacity_full (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (face : ∀ v, D.Triangle (N.star v))
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (root : V) (hbroot : black root) (S : Finset F)
    (hr : ∀ i, (face root).corner i ∉ S) :
    2*S.card ≤ ∑ v ∈ Finset.univ.filter black,
      min 2 ((Finset.univ.filter fun i => (face v).corner i ∈ S).card) := by
  have hd := N.induced_density D h hN h3 hcut htr black hc root hbroot Sᶜ
    ((face root).all_corners D Sᶜ |>.mpr (by simpa using hr))
  have hi := N.capacity_identity D face black hc Sᶜ
  simp only [Finset.mem_compl,not_not] at hi
  have hu := Finset.card_add_card_compl S
  have hb := N.black_dual_card D h hN h3 black hc
  simp only [← Nat.cast_sum] at hi
  omega

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.BMatching ----
namespace OAI

/-! Integral flows, capacitated matchings, and incidence-state pairs. -/

namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

theorem gadget_matching (R : A → B → Prop) (hcard : Fintype.card A = Fintype.card B)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card)) :
    ∃ f : Left R ≃ Right R, ∀ l, gadget R l (f l) := by
  obtain ⟨f,hfi,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective (gadget R)).mp
    (gadget_hall R hcap)
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,by
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,hcard]⟩
  exact ⟨Equiv.ofBijective f hb,hf⟩

end
end Barnette.BMatching
namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

lemma two_image_count {C : Type*} [Fintype C] (f : Fin 2 → C) (hf : Function.Injective f) :
    (Finset.univ.filter fun c => ∃ k, f k = c).card = 2 := by
  have hs : (Finset.univ.filter fun c => ∃ k, f k = c) = Finset.univ.image f := by ext; simp
  rw [hs,Finset.card_image_of_injective _ hf]
  simp

lemma data_two_factor (R : A → B → Prop) (M : FactorData R) :
    ∃ Q : A → B → Prop, (∀ a b, Q a b → R a b) ∧
      (∀ a, (Finset.univ.filter (Q a)).card = 2) ∧
      (∀ b, (Finset.univ.filter fun a => Q a b).card = 2) := by
  classical
  let Q : A → B → Prop := fun a b => ∃ k, (M.left (a,k)).val.2 = b
  have hQright (a : A) (b : B) : Q a b ↔ ∃ k, (M.right (b,k)).val.1 = a := by
    constructor
    · rintro ⟨k,hk⟩
      have he : M.left (a,k) ∈ Set.range M.right := M.same_range ▸ Set.mem_range_self _
      obtain ⟨⟨c,j⟩,he⟩ := he
      have hc : c = b := (M.right_coord c j).symm.trans ((congrArg (fun e : Inc R => e.val.2) he).trans hk)
      subst c
      exact ⟨j,(congrArg (fun e : Inc R => e.val.1) he).trans (M.left_coord a k)⟩
    · rintro ⟨k,hk⟩
      have he : M.right (b,k) ∈ Set.range M.left := M.same_range.symm ▸ Set.mem_range_self _
      obtain ⟨⟨c,j⟩,he⟩ := he
      have hc : c = a := (M.left_coord c j).symm.trans ((congrArg (fun e : Inc R => e.val.1) he).trans hk)
      subst c
      exact ⟨j,(congrArg (fun e : Inc R => e.val.2) he).trans (M.right_coord b k)⟩
  refine ⟨Q,?_,?_,?_⟩
  · rintro a b ⟨k,rfl⟩
    have h := (M.left (a,k)).property
    rwa [M.left_coord] at h
  · intro a
    have hi : Function.Injective (fun k => (M.left (a,k)).val.2) := by
      intro i j hij
      have he : M.left (a,i) = M.left (a,j) := Subtype.ext (Prod.ext (by simp [M.left_coord]) hij)
      exact Prod.mk.inj (M.left.injective he) |>.2
    simpa only [Q] using two_image_count (fun k => (M.left (a,k)).val.2) hi
  · intro b
    simp only [hQright]
    apply two_image_count
    intro i j hij
    have he : M.right (b,i) = M.right (b,j) := Subtype.ext (Prod.ext hij (by simp [M.right_coord]))
    exact Prod.mk.inj (M.right.injective he) |>.2

lemma regular_hall (Q : A → B → Prop) (n : ℕ) (hn : 0 < n)
    (hrow : ∀ a, (Finset.univ.filter (Q a)).card = n)
    (hcol : ∀ b, (Finset.univ.filter fun a => Q a b).card = n)
    (S : Finset A) :
    S.card ≤ (Finset.univ.filter fun b => ∃ a ∈ S, Q a b).card := by
  let T := Finset.univ.filter fun b => ∃ a ∈ S, Q a b
  have hc : n*S.card = ∑ b, (S.filter fun a => Q a b).card := by
    calc
      _ = ∑ a ∈ S, (Finset.univ.filter (Q a)).card := by simp [hrow,mul_comm]
      _ = _ := by simp only [Finset.card_filter]; rw [Finset.sum_comm]
  have hl : ∑ b, (S.filter fun a => Q a b).card ≤ ∑ b, if b ∈ T then n else 0 := by
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : b ∈ T
    · simp only [hb,ite_true]
      rw [← hcol b]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    · have hnone : ∀ a ∈ S, ¬Q a b := by simpa [T] using hb
      simp [hb,Finset.filter_false_of_mem hnone]
  have hr : (∑ b, if b ∈ T then n else 0) = n*T.card := by simp [mul_comm]
  rw [hr,← hc] at hl
  exact Nat.le_of_mul_le_mul_left hl hn

lemma regular_matching (Q : A → B → Prop) (hcard : Fintype.card A = Fintype.card B)
    (n : ℕ) (hn : 0 < n)
    (hrow : ∀ a, (Finset.univ.filter (Q a)).card = n)
    (hcol : ∀ b, (Finset.univ.filter fun a => Q a b).card = n) :
    ∃ f : A ≃ B, ∀ a, Q a (f a) := by
  obtain ⟨f,hfi,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective Q).mp
    (regular_hall Q n hn hrow hcol)
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,hcard⟩),hf⟩

theorem two_matchings (R : A → B → Prop) (hcard : Fintype.card A = Fintype.card B)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card)) :
    ∃ f g : A ≃ B, (∀ a, R a (f a) ∧ R a (g a)) ∧ (∀ a, f a ≠ g a) := by
  classical
  obtain ⟨p,hp⟩ := gadget_matching R hcard hcap
  obtain ⟨M⟩ := data_of_gadget R p hp
  obtain ⟨Q,hQR,hrow,hcol⟩ := data_two_factor R M
  obtain ⟨f,hf⟩ := regular_matching Q hcard 2 (by decide) hrow hcol
  let Q' : A → B → Prop := fun a b => Q a b ∧ b ≠ f a
  have hr : ∀ a, (Finset.univ.filter (Q' a)).card = 1 := by
    intro a
    have he : Finset.univ.filter (Q' a) = (Finset.univ.filter (Q a)).erase (f a) := by
      ext b; simp [Q',and_comm]
    rw [he,Finset.card_erase_of_mem (by simp [hf a]),hrow]
  have hc : ∀ b, (Finset.univ.filter fun a => Q' a b).card = 1 := by
    intro b
    have he : (Finset.univ.filter fun a => Q' a b) =
        (Finset.univ.filter fun a => Q a b).erase (f.symm b) := by
      ext a
      simp only [Q',Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
      constructor
      · rintro ⟨hq,hne⟩
        exact ⟨fun he => hne (by rw [he,f.apply_symm_apply]),hq⟩
      · rintro ⟨hne,hq⟩
        exact ⟨hq,fun he => hne (f.injective (by simpa using he.symm))⟩
    rw [he,Finset.card_erase_of_mem (by simpa using hf (f.symm b)),hcol]
  obtain ⟨g,hg⟩ := regular_matching Q' hcard 1 (by decide) (by simpa only [Q'] using hr) (by simpa only [Q'] using hc)
  exact ⟨f,g,fun a => ⟨hQR _ _ (hf a),hQR _ _ (hg a).1⟩,fun a h => (hg a).2 h.symm⟩

end
end Barnette.BMatching
namespace Barnette.TriangleSystem.State
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}
lemma exists_value (r : A ≃ X) (hr : ∀ t, (r t : V) ∈ Set.range (T.vertex t)) :
    ∃ s : T.State X, ∀ t, s.value t = (r t : V) := by
  choose c hc using hr
  refine ⟨⟨c,?_,?_⟩,hc⟩
  · intro t u h
    exact r.injective (Subtype.ext (by simpa only [hc] using h))
  · ext v
    constructor
    · rintro ⟨t,rfl⟩
      change T.vertex t (c t) ∈ X
      rw [hc]; exact (r t).property
    · intro hv
      obtain ⟨t,ht⟩ := r.surjective ⟨v,hv⟩
      exact ⟨t,(hc t).trans (congrArg Subtype.val ht)⟩
end Barnette.TriangleSystem.State

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

lemma nonroots_card (root : V) (hr : M.black root) :
    Fintype.card (M.nonroots root) = Fintype.card (M.Black root) := by
  have hf := N.black_dual_card D M.duality M.simple M.cubic M.black M.coloring
  have hc : Fintype.card (Set.range (M.face root).corner) = 3 := by
    rw [← Fintype.card_congr (Equiv.ofInjective _ (M.face root).corner_injective)]
    rfl
  have hn := Fintype.card_compl_set (Set.range (M.face root).corner)
  have hb : Fintype.card (M.Black root) = (Finset.univ.filter M.black).card - 1 := by
    rw [Fintype.card_subtype]
    have he : (Finset.univ.filter fun v => M.black v ∧ v ≠ root) =
        (Finset.univ.filter M.black).erase root := by ext; simp [and_comm]
    rw [he,Finset.card_erase_of_mem (by simp [hr])]
  have hnx : Fintype.card (M.nonroots root) =
      Fintype.card F - Fintype.card (Set.range (M.face root).corner) := by
    convert hn using 1
    congr!
  rw [hnx,hc,hb,hf]
  omega

omit [Fintype F] in
lemma corner_filter_card (root : V) (S : Finset (M.nonroots root)) (t : M.Black root) :
    (S.filter fun x => x.val ∈ Set.range (M.face t.val).corner).card =
      (Finset.univ.filter fun i => (M.face t.val).corner i ∈ S.image Subtype.val).card := by
  have he : (S.filter fun x => x.val ∈ Set.range (M.face t.val).corner).image Subtype.val =
      (Finset.univ.filter fun i => (M.face t.val).corner i ∈ S.image Subtype.val).image
        (M.face t.val).corner := by
    ext z
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_range]
    constructor
    · rintro ⟨x,⟨hx,i,hi⟩,rfl⟩
      exact ⟨i,⟨x,hx,hi.symm⟩,hi⟩
    · rintro ⟨i,⟨x,hx,hxi⟩,hi⟩
      exact ⟨x,⟨hx,i,hxi.symm⟩,hxi.trans hi⟩
  have hh := congrArg Finset.card he
  rwa [Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_image_of_injective _ (M.face t.val).corner_injective] at hh

lemma state_capacity (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (root : V) (hr : M.black root) (S : Finset (M.nonroots root)) :
    2*S.card ≤ ∑ t : M.Black root,
      min 2 ((S.filter fun x => x.val ∈ Set.range (M.face t.val).corner).card) := by
  let U := S.image Subtype.val
  have hu : ∀ i, (M.face root).corner i ∉ U := by
    intro i hi
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hi
    exact x.property ⟨i,hx.symm⟩
  have hcap := N.capacity_full D M.duality M.simple M.cubic hcut htr M.face M.black
    M.coloring root hr U hu
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcap
  have hz : min 2 ((Finset.univ.filter fun i => (M.face root).corner i ∈ U).card) = 0 := by
    have hh : (Finset.univ.filter fun i => (M.face root).corner i ∈ U) = ∅ := by
      ext i; simp [hu]
    rw [hh]; simp
  have he : (∑ v ∈ Finset.univ.filter M.black,
        min 2 ((Finset.univ.filter fun i => (M.face v).corner i ∈ U).card)) =
      ∑ t : M.Black root, min 2 ((Finset.univ.filter fun i => (M.face t.val).corner i ∈ U).card) := by
    rw [← Finset.sum_erase_add _ _ (show root ∈ Finset.univ.filter M.black by simp [hr]),hz,add_zero]
    apply Finset.sum_subtype
    intro v; simp [and_comm]
  rw [he] at hcap
  simpa only [M.corner_filter_card root S] using hcap

theorem pair_nonempty (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (root : V) (hr : M.black root) : Nonempty ((M.system root).Pair (M.nonroots root)) := by
  obtain ⟨f,g,hfg,hne⟩ := Barnette.BMatching.two_matchings
    (fun (x : M.nonroots root) (t : M.Black root) => x.val ∈ Set.range (M.face t.val).corner)
    (M.nonroots_card root hr) (by
      intro S
      convert M.state_capacity hcut htr root hr S using 1; congr!)
  have hf : ∀ t : M.Black root, (f.symm t : F) ∈ Set.range ((M.system root).vertex t) := by
    intro t
    have h := (hfg (f.symm t)).1
    rw [f.apply_symm_apply] at h
    exact h
  have hg : ∀ t : M.Black root, (g.symm t : F) ∈ Set.range ((M.system root).vertex t) := by
    intro t
    have h := (hfg (g.symm t)).2
    rw [g.apply_symm_apply] at h
    exact h
  obtain ⟨r,hrv⟩ := Barnette.TriangleSystem.State.exists_value f.symm hf
  obtain ⟨s,hsv⟩ := Barnette.TriangleSystem.State.exists_value g.symm hg
  refine ⟨⟨(r,s),?_⟩⟩
  intro t he
  rw [hrv,hsv] at he
  have hh : f.symm t = g.symm t := Subtype.ext he
  apply hne (f.symm t)
  rw [f.apply_symm_apply,hh,g.apply_symm_apply]

end
end Barnette.Network.ColoredDual

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network OAI.Barnette.Network.ColoredDual
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.ColoredDual.pair_nonempty := @_root_.OAI.Barnette.Network.ColoredDual.pair_nonempty
