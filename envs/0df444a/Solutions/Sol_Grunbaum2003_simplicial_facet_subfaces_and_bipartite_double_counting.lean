-- Prove2me | solution 1 for Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T03:24:27.632285+00:00
-- url     : https://prove2.me/submissions/b5f7742c-4240-4be6-9d2a-0d61dd0d1f9c

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card

set_option autoImplicit false
open scoped BigOperators Classical

noncomputable section

namespace Grunbaum2003

/-- If `{x}` is an exposed singleton of `P`, `v : ι → (Fin d → ℝ)` maps into `P`, and
`x ∈ convexHull ℝ (Set.range v)`, then `x ∈ Set.range v`. -/
theorem exposed_singleton_mem_range_of_mem_convexHull {d : ℕ} {ι : Type*} [Fintype ι]
    {P : Set (Fin d → ℝ)} {x : Fin d → ℝ} (hx : IsExposed ℝ P {x})
    {v : ι → Fin d → ℝ} (hvP : ∀ i : ι, v i ∈ P)
    (hxHull : x ∈ convexHull ℝ (Set.range v)) :
    x ∈ Set.range v := by
  obtain ⟨l, hl⟩ := hx (Set.singleton_nonempty x)
  have hxMem : x ∈ {y ∈ P | ∀ z ∈ P, l z ≤ l y} := hl ▸ Set.mem_singleton x
  have hlv : ∀ i : ι, l (v i) ≤ l x := fun i => hxMem.2 (v i) (hvP i)
  have hxFin : x ∈ convexHull ℝ (↑(Finset.univ.image v) : Set (Fin d → ℝ)) := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hxHull
  rw [Finset.mem_convexHull'] at hxFin
  obtain ⟨w, hw0, hw1, hwx⟩ := hxFin
  have hExistsPos : ∃ y ∈ Finset.univ.image v, 0 < w y := by
    by_contra! hAllZero
    have hSumZero : ∑ y ∈ Finset.univ.image v, w y = 0 :=
      Finset.sum_eq_zero (fun y hy => le_antisymm (hAllZero y hy) (hw0 y hy))
    linarith
  obtain ⟨y₀, hy₀, hwPos⟩ := hExistsPos
  obtain ⟨i₀, _, rfl⟩ := Finset.mem_image.mp hy₀
  have hDiffNonneg : ∀ y ∈ Finset.univ.image v, 0 ≤ w y * (l x - l y) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact mul_nonneg (hw0 (v i) hy) (sub_nonneg.mpr (hlv i))
  have hDiffSumZero : ∑ y ∈ Finset.univ.image v, w y * (l x - l y) = 0 := by
    have hlin :
        (∑ y ∈ Finset.univ.image v, w y * (l x - l y)) =
          (∑ y ∈ Finset.univ.image v, w y) * l x -
            l (∑ y ∈ Finset.univ.image v, w y • y) := by
      rw [Finset.sum_mul, map_sum]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro y _
      rw [map_smul, smul_eq_mul, mul_sub]
    rw [hlin, hw1, hwx, one_mul, sub_self]
  have hTermZero : w (v i₀) * (l x - l (v i₀)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hDiffNonneg).mp hDiffSumZero (v i₀) hy₀
  have hEqL : l (v i₀) = l x := by
    rcases mul_eq_zero.mp hTermZero with hwZero | hSubZero
    · linarith
    · linarith
  have hvi₀Mem : v i₀ ∈ ({x} : Set (Fin d → ℝ)) := by
    rw [hl]
    exact ⟨hvP i₀, fun z hz => (hxMem.2 z hz).trans_eq hEqL.symm⟩
  have hvi₀Eq : v i₀ = x := Set.mem_singleton_iff.mp hvi₀Mem
  exact ⟨i₀, hvi₀Eq⟩

/-- For any exposed facet `F` of `P` that is the convex hull of an affinely independent family
`v : Fin d → (Fin d → ℝ)`, every `v i` is an exposed vertex of `P`, the set of exposed vertices
of `P` in `F` is `Set.range v`, and its cardinality is `d`. -/
theorem simplicial_facet_exposed_vertices_eq_range {d : ℕ} {P : Set (Fin d → ℝ)}
    (hHull : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (F : Set (Fin d → ℝ)) (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    (hRankF : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d)
    (v : Fin d → Fin d → ℝ) (hv : AffineIndependent ℝ v)
    (hFEq : F = convexHull ℝ (Set.range v)) :
    Function.Injective v ∧
    (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
    F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v ∧
    (F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).ncard = d := by
  have hvInj : Function.Injective v := hv.injective
  have hvF : ∀ i : Fin d, v i ∈ F := by
    intro i
    rw [hFEq]
    exact subset_convexHull ℝ (Set.range v) ⟨i, rfl⟩
  have hvP : ∀ i : Fin d, v i ∈ P := fun i => hF.subset (hvF i)
  let I : Finset (Fin d) := Finset.univ.filter (fun i => IsExposed ℝ P {v i})
  have hInterEq :
      F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (I : Set (Fin d)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe,
      I, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxF, hxExp⟩
      rw [hFEq] at hxF
      obtain ⟨i, rfl⟩ := exposed_singleton_mem_range_of_mem_convexHull hxExp hvP hxF
      exact ⟨i, hxExp, rfl⟩
    · rintro ⟨i, hiExp, rfl⟩
      exact ⟨hvF i, hiExp⟩
  have hFHullI : F = convexHull ℝ (v '' (I : Set (Fin d))) := by
    have h := hHull.2 ⟨F, hF⟩
    rwa [hInterEq] at h
  have hIne : I.Nonempty := by
    have hVne : (v '' (I : Set (Fin d))).Nonempty := by
      apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
      rwa [← hFHullI]
    rcases hVne with ⟨_, ⟨i, hi, rfl⟩⟩
    exact ⟨i, hi⟩
  have hSpanEq : affineSpan ℝ (v '' (I : Set (Fin d))) = affineSpan ℝ F := by
    conv_rhs => rw [hFHullI]
    exact (affineSpan_convexHull (v '' (I : Set (Fin d)))).symm
  have hCardI : I.card = d := by
    have hCardPos : 0 < I.card := Finset.Nonempty.card_pos hIne
    have hc : I.card = (I.card - 1) + 1 := (Nat.sub_add_cancel hCardPos).symm
    have h1 := hv.finrank_vectorSpan_image_finset hc
    rw [← direction_affineSpan, Finset.coe_image, hSpanEq] at h1
    omega
  have hIUniv : I = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    rw [hCardI, Finset.card_univ, Fintype.card_fin]
  have hvExp : ∀ i : Fin d, IsExposed ℝ P {v i} := by
    intro i
    have hi : i ∈ I := hIUniv ▸ Finset.mem_univ i
    exact (Finset.mem_filter.mp hi).2
  have hInterRange : F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v := by
    rw [hInterEq, hIUniv, Finset.coe_univ, Set.image_univ]
  have hNcard : (F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).ncard = d := by
    rw [hInterEq, Set.InjOn.ncard_image hvInj.injOn, Set.ncard_coe_finset, hCardI]
  exact ⟨hvInj, hvExp, hInterRange, hNcard⟩

/-- Every facet `F` of a simplicial `d`-polytope `P` (`IsSimplicialDPolytope P`) is the convex
hull of `d` distinct exposed vertices of `P` and contains exactly `d` exposed vertices of `P`. -/
theorem isSimplicialDPolytope_facet_exposed_vertices {d : ℕ} {P : Set (Fin d → ℝ)}
    (hP : IsSimplicialDPolytope P)
    (hHull : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}))
    (F : Set (Fin d → ℝ)) (hFne : F.Nonempty) (hF : IsExposed ℝ P F)
    (hRankF : Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d) :
    ∃ v : Fin d → Fin d → ℝ,
      AffineIndependent ℝ v ∧
      Function.Injective v ∧
      (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
      F = convexHull ℝ (Set.range v) ∧
      F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v ∧
      (F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).ncard = d := by
  obtain ⟨v, hv, hFEq⟩ := hP.2 F hFne hF hRankF
  obtain ⟨hvInj, hvExp, hInter, hNcard⟩ :=
    simplicial_facet_exposed_vertices_eq_range hHull F hFne hF hRankF v hv hFEq
  exact ⟨v, hv, hvInj, hvExp, hFEq, hInter, hNcard⟩

end Grunbaum2003

namespace Grunbaum2003

/-- For any family `v : ι → Fin d → ℝ` of exposed vertices of `P` and any finite subset `s : Finset ι`,
the exposed vertices of `P` lying in `convexHull ℝ (v '' (s : Set ι))` are exactly `v '' (s : Set ι)`. -/
theorem exposed_vertices_inter_convexHull_image_eq
    {d : ℕ} {P : Set (Fin d → ℝ)} {ι : Type*}
    (v : ι → Fin d → ℝ)
    (hvExp : ∀ i : ι, IsExposed ℝ P {v i})
    (s : Finset ι) :
    convexHull ℝ (v '' (s : Set ι)) ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set ι) := by
  ext x
  constructor
  · rintro ⟨hxHull, hxExp⟩
    have hRange : v '' (s : Set ι) = Set.range (fun j : s => v j.val) := by
      ext y
      simp
    rw [hRange] at hxHull ⊢
    exact exposed_singleton_mem_range_of_mem_convexHull hxExp
      (fun j => (hvExp j.val).subset (Set.mem_singleton (v j.val))) hxHull
  · rintro ⟨i, hi, rfl⟩
    exact ⟨subset_convexHull ℝ (v '' (s : Set ι)) ⟨i, hi, rfl⟩, hvExp i⟩

/-- If `v : Fin d → Fin d → ℝ` is an injective family of exposed vertices of `P`, then the map
sending a vertex index subset `s : Finset (Fin d)` to `convexHull ℝ (v '' (s : Set (Fin d)))`
is injective. -/
theorem simplicial_facet_subface_hull_injective
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (v : Fin d → Fin d → ℝ)
    (hvInj : Function.Injective v)
    (hvExp : ∀ i : Fin d, IsExposed ℝ P {v i})
    (s₁ s₂ : Finset (Fin d)) :
    convexHull ℝ (v '' (s₁ : Set (Fin d))) = convexHull ℝ (v '' (s₂ : Set (Fin d))) ↔
      s₁ = s₂ := by
  constructor
  · intro hEq
    have hInter :
        convexHull ℝ (v '' (s₁ : Set (Fin d))) ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} =
          convexHull ℝ (v '' (s₂ : Set (Fin d))) ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
      congrArg (fun A => A ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) hEq
    rw [exposed_vertices_inter_convexHull_image_eq v hvExp,
      exposed_vertices_inter_convexHull_image_eq v hvExp] at hInter
    have hSetEq : (s₁ : Set (Fin d)) = (s₂ : Set (Fin d)) :=
      hvInj.image_injective hInter
    exact Finset.coe_inj.mp hSetEq
  · intro hEq
    rw [hEq]

/-- Double counting on a finite bipartite incidence relation `(ℱ, ℛ, inc)`:
if every `F ∈ ℱ` is incident to `a` elements of `ℛ` and every `R ∈ ℛ` is incident to `b`
elements of `ℱ`, then `a * ℱ.card = b * ℛ.card`. -/
theorem bipartite_incidence_double_count {α β : Type*}
    (ℱ : Finset α) (ℛ : Finset β) (inc : α → β → Prop)
    (a b : ℕ)
    (hF : ∀ F ∈ ℱ, (ℛ.filter (fun R => inc F R)).card = a)
    (hR : ∀ R ∈ ℛ, (ℱ.filter (fun F => inc F R)).card = b) :
    a * ℱ.card = b * ℛ.card := by
  have hL :
      (∑ F ∈ ℱ, ∑ R ∈ ℛ, if inc F R then (1 : ℕ) else 0) = a * ℱ.card := by
    have h1 : ∀ F ∈ ℱ,
        (∑ R ∈ ℛ, if inc F R then (1 : ℕ) else 0) = a := by
      intro F hFmem
      rw [← Finset.card_filter]
      exact hF F hFmem
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hRight :
      (∑ R ∈ ℛ, ∑ F ∈ ℱ, if inc F R then (1 : ℕ) else 0) = b * ℛ.card := by
    have h2 : ∀ R ∈ ℛ,
        (∑ F ∈ ℱ, if inc F R then (1 : ℕ) else 0) = b := by
      intro R hRmem
      rw [← Finset.card_filter]
      exact hR R hRmem
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  rw [← hL, ← hRight, Finset.sum_comm]

/-- Polygon vertex-edge incidence corollary (`a = 2, b = 2`): if every edge contains 2 vertices
and every vertex lies in 2 edges, then `ℰ.card = V.card`. -/
theorem polygon_edge_vertex_card_eq {α β : Type*}
    (ℰ : Finset α) (V : Finset β) (inc : α → β → Prop)
    (hE : ∀ E ∈ ℰ, (V.filter (fun v => inc E v)).card = 2)
    (hV : ∀ v ∈ V, (ℰ.filter (fun E => inc E v)).card = 2) :
    ℰ.card = V.card := by
  have h := bipartite_incidence_double_count ℰ V inc 2 2 hE hV
  omega

/-- Simplicial 3-polytope facet-edge incidence corollary (`a = 3, b = 2`): if every triangular
facet contains 3 edges and every edge lies in 2 facets, then `3 * ℱ.card = 2 * ℰ.card`. -/
theorem simplicial_three_polytope_facet_edge_count {α β : Type*}
    (ℱ : Finset α) (ℰ : Finset β) (inc : α → β → Prop)
    (hF : ∀ F ∈ ℱ, (ℰ.filter (fun E => inc F E)).card = 3)
    (hE : ∀ E ∈ ℰ, (ℱ.filter (fun F => inc F E)).card = 2) :
    3 * ℱ.card = 2 * ℰ.card :=
  bipartite_incidence_double_count ℱ ℰ inc 3 2 hF hE

end Grunbaum2003

namespace Grunbaum2003

theorem simplicial_facet_subfaces_and_bipartite_double_counting_proved :
  (∀ {d : ℕ} {P : Set (Fin d → ℝ)} (v : Fin d → Fin d → ℝ),
    Function.Injective v →
    (∀ i : Fin d, IsExposed ℝ P {v i}) →
    (∀ s : Finset (Fin d),
      convexHull ℝ (v '' (s : Set (Fin d))) ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} =
        v '' (s : Set (Fin d))) ∧
    (∀ s₁ s₂ : Finset (Fin d),
      convexHull ℝ (v '' (s₁ : Set (Fin d))) = convexHull ℝ (v '' (s₂ : Set (Fin d))) ↔
        s₁ = s₂)) ∧
  (∀ {α β : Type} (ℱ : Finset α) (ℛ : Finset β) (inc : α → β → Prop) (a b : ℕ),
    (∀ F ∈ ℱ, (ℛ.filter (fun R => inc F R)).card = a) →
    (∀ R ∈ ℛ, (ℱ.filter (fun F => inc F R)).card = b) →
    a * ℱ.card = b * ℛ.card) ∧
  (∀ {α β : Type} (ℰ : Finset α) (V : Finset β) (inc : α → β → Prop),
    (∀ E ∈ ℰ, (V.filter (fun v => inc E v)).card = 2) →
    (∀ v ∈ V, (ℰ.filter (fun E => inc E v)).card = 2) →
    ℰ.card = V.card) ∧
  (∀ {α β : Type} (ℱ : Finset α) (ℰ : Finset β) (inc : α → β → Prop),
    (∀ F ∈ ℱ, (ℰ.filter (fun E => inc F E)).card = 3) →
    (∀ E ∈ ℰ, (ℱ.filter (fun F => inc F E)).card = 2) →
    3 * ℱ.card = 2 * ℰ.card) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d P v hvInj hvExp
    exact ⟨exposed_vertices_inter_convexHull_image_eq v hvExp,
      simplicial_facet_subface_hull_injective v hvInj hvExp⟩
  · intro α β ℱ ℛ inc a b hF hR
    exact bipartite_incidence_double_count ℱ ℛ inc a b hF hR
  · intro α β ℰ V inc hE hV
    exact polygon_edge_vertex_card_eq ℰ V inc hE hV
  · intro α β ℱ ℰ inc hF hE
    exact simplicial_three_polytope_facet_edge_count ℱ ℰ inc hF hE

end Grunbaum2003

end

open Grunbaum2003 in
theorem solution :
  (∀ {d : ℕ} {P : Set (Fin d → ℝ)} (v : Fin d → Fin d → ℝ),
    Function.Injective v →
    (∀ i : Fin d, IsExposed ℝ P {v i}) →
    (∀ s : Finset (Fin d),
      convexHull ℝ (v '' (s : Set (Fin d))) ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} =
        v '' (s : Set (Fin d))) ∧
    (∀ s₁ s₂ : Finset (Fin d),
      convexHull ℝ (v '' (s₁ : Set (Fin d))) = convexHull ℝ (v '' (s₂ : Set (Fin d))) ↔
        s₁ = s₂)) ∧
  (∀ {α β : Type} (ℱ : Finset α) (ℛ : Finset β) (inc : α → β → Prop) (a b : ℕ),
    (∀ F ∈ ℱ, (ℛ.filter (fun R => inc F R)).card = a) →
    (∀ R ∈ ℛ, (ℱ.filter (fun F => inc F R)).card = b) →
    a * ℱ.card = b * ℛ.card) ∧
  (∀ {α β : Type} (ℰ : Finset α) (V : Finset β) (inc : α → β → Prop),
    (∀ E ∈ ℰ, (V.filter (fun v => inc E v)).card = 2) →
    (∀ v ∈ V, (ℰ.filter (fun E => inc E v)).card = 2) →
    ℰ.card = V.card) ∧
  (∀ {α β : Type} (ℱ : Finset α) (ℰ : Finset β) (inc : α → β → Prop),
    (∀ F ∈ ℱ, (ℰ.filter (fun E => inc F E)).card = 3) →
    (∀ E ∈ ℰ, (ℱ.filter (fun F => inc F E)).card = 2) →
    3 * ℱ.card = 2 * ℰ.card) :=
  Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting_proved
