-- Prove2me | solution 1 for Grunbaum2003.simplicial_facet_exposed_vertices_and_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T02:56:10.884655+00:00
-- url     : https://prove2.me/submissions/710b128c-19cd-4672-aea2-9cfcbb4fb6fd

import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Data.Finset.Image
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent

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

theorem simplicial_facet_exposed_vertices_and_cardinality_proved :
  ∀ {d : ℕ} {P : Set (Fin d → ℝ)},
    IsSimplicialDPolytope P →
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ∀ (F : Set (Fin d → ℝ)), F.Nonempty → IsExposed ℝ P F →
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d →
      ∃ v : Fin d → Fin d → ℝ,
        AffineIndependent ℝ v ∧
        Function.Injective v ∧
        (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
        F = convexHull ℝ (Set.range v) ∧
        F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v ∧
        (F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).ncard = d := by
  intro d P hP hHull F hFne hF hRankF
  exact isSimplicialDPolytope_facet_exposed_vertices hP hHull F hFne hF hRankF

end Grunbaum2003

end

open Grunbaum2003 in
theorem solution :
  ∀ {d : ℕ} {P : Set (Fin d → ℝ)},
    IsSimplicialDPolytope P →
    ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
    ∀ (F : Set (Fin d → ℝ)), F.Nonempty → IsExposed ℝ P F →
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d →
      ∃ v : Fin d → Fin d → ℝ,
        AffineIndependent ℝ v ∧
        Function.Injective v ∧
        (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
        F = convexHull ℝ (Set.range v) ∧
        F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v ∧
        (F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).ncard = d :=
  Grunbaum2003.simplicial_facet_exposed_vertices_and_cardinality_proved
