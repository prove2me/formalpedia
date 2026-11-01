-- Prove2me | solution 1 for Grunbaum2003.boundary_refines_simplex_zero_dim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:17:23.414493+00:00
-- url     : https://prove2.me/submissions/0ab8bd4a-92d4-4ee0-bcae-966b96fff6a2

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic

set_option autoImplicit false

namespace Grunbaum2003

theorem eq_singleton_zero_of_nonempty_fin_zero {S : Set (Fin 0 → ℝ)} (hS : S.Nonempty) :
    S = {0} := by
  rcases hS with ⟨x, hx⟩
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro _
    exact Subsingleton.elim y 0
  · rintro rfl
    have hxz : x = 0 := Subsingleton.elim x 0
    rwa [← hxz]

theorem sUnion_boundaryFaces_eq_empty_of_eq_singleton_zero {S : Set (Fin 0 → ℝ)}
    (hS : S = {0}) : ⋃₀ boundaryFaces S = ∅ := by
  ext x
  simp only [Set.mem_sUnion, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro F hF hxF
  rcases hF with ⟨hFe, hFneS⟩
  have hsub : F ⊆ {0} := hS ▸ hFe.subset
  have hx0 : x = 0 := Subsingleton.elim x 0
  subst hx0
  have hFeq : F = {0} := Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hxF)
  exact hFneS (hFeq.trans hS.symm)

/-- Grünbaum (2003), §11.1 (Theorem 11.1.1, p. 200): in dimension `d = 0`, the boundary
complex of every `0`-polytope `P` refines the boundary complex of every `0`-simplex
(both having the empty carrier and sole boundary face `∅`). -/
theorem boundary_refines_simplex_zero_dim
    (P : Set (Fin 0 → ℝ)) (hP : IsDPolytope P)
    (v : Fin 1 → (Fin 0 → ℝ)) (_hv : AffineIndependent ℝ v) :
    BoundaryRefines P (convexHull ℝ (Set.range v)) := by
  obtain ⟨⟨Vset, _, hVne, hPhull⟩, _⟩ := hP
  have hPne : P.Nonempty := by
    rw [hPhull]
    exact hVne.convexHull
  have hQne : (convexHull ℝ (Set.range v)).Nonempty :=
    (Set.range_nonempty v).convexHull
  have hP0 : P = {0} := eq_singleton_zero_of_nonempty_fin_zero hPne
  have hQ0 : convexHull ℝ (Set.range v) = {0} := eq_singleton_zero_of_nonempty_fin_zero hQne
  have hPB : ⋃₀ boundaryFaces P = ∅ := sUnion_boundaryFaces_eq_empty_of_eq_singleton_zero hP0
  have hQB : ⋃₀ boundaryFaces (convexHull ℝ (Set.range v)) = ∅ :=
    sUnion_boundaryFaces_eq_empty_of_eq_singleton_zero hQ0
  haveI : IsEmpty (⋃₀ boundaryFaces P) := by
    rw [hPB]; infer_instance
  haveI : IsEmpty (⋃₀ boundaryFaces (convexHull ℝ (Set.range v))) := by
    rw [hQB]; infer_instance
  let e : (⋃₀ boundaryFaces P) ≃ (⋃₀ boundaryFaces (convexHull ℝ (Set.range v))) :=
    Equiv.equivOfIsEmpty _ _
  refine ⟨{
    toEquiv := e
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology
  }, ?_⟩
  intro K _
  refine ⟨{∅}, Set.finite_singleton ∅, ?_, ?_, ?_⟩
  · intro F hF
    rw [Set.mem_singleton_iff] at hF
    subst hF
    refine ⟨fun h => (Set.not_nonempty_empty h).elim, ?_⟩
    rw [hP0]
    exact Set.singleton_nonempty 0 |>.ne_empty.symm
  · intro F hF G hGe
    rw [Set.mem_singleton_iff] at hF ⊢
    subst hF
    exact Set.subset_empty_iff.mp hGe.subset
  · intro x
    exact isEmptyElim x

end Grunbaum2003

theorem solution
    (P : Set (Fin 0 → ℝ)) (hP : Grunbaum2003.IsDPolytope P)
    (v : Fin 1 → (Fin 0 → ℝ)) (hv : AffineIndependent ℝ v) :
    Grunbaum2003.BoundaryRefines P (convexHull ℝ (Set.range v)) :=
  Grunbaum2003.boundary_refines_simplex_zero_dim P hP v hv
