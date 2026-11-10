-- Prove2me | solution 1 for Grunbaum2003.exists_stellar_subdivision_face_finset_bijection
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:44:38.635537+00:00
-- url     : https://prove2.me/submissions/3055e091-3477-4c84-83aa-15ff476ebbe1

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_stellar_cone_face_injective_disjoint_and_equiv
import Theorems.Thm_Grunbaum2003_exists_stellar_subdivision_cone_decomposition
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
open scoped Classical

open Grunbaum2003

theorem solution (d : ℕ) (hd : 4 ≤ d)
    (P : Set (Fin d → ℝ)) (hP : IsSimplicialDPolytope P)
    (ℱ : ℕ → Finset (Set (Fin d → ℝ)))
    (hℱ : ∀ k : ℕ, (ℱ k : Set (Set (Fin d → ℝ))) =
      {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
      (ℱ k).card = faceCount P k) :
    ∃ (P' : Set (Fin d → ℝ)) (F₀ : Set (Fin d → ℝ))
      (ℱ' ℱ_new : ℕ → Finset (Set (Fin d → ℝ))),
      IsSimplicialDPolytope P' ∧
      F₀ ∈ ℱ (d - 1) ∧
      (∀ k : ℕ, (ℱ' k : Set (Set (Fin d → ℝ))) =
        {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P' F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
        (ℱ' k).card = faceCount P' k) ∧
      (∀ j : Fin d, j.val + 1 < d →
        ℱ' j.val = ℱ j.val ∪ ℱ_new j.val ∧
        Disjoint (ℱ j.val) (ℱ_new j.val) ∧
        Nonempty (ℱ_new j.val ≃ (Finset.univ : Finset (Fin d)).powersetCard j.val)) ∧
      (ℱ' (d - 1) = (ℱ (d - 1)).erase F₀ ∪ ℱ_new (d - 1) ∧
        Disjoint ((ℱ (d - 1)).erase F₀) (ℱ_new (d - 1)) ∧
        Nonempty (ℱ_new (d - 1) ≃ (Finset.univ : Finset (Fin d)).powersetCard (d - 1))) := by
  obtain ⟨P', F₀, y, v, ℱ', hP', hF₀, hy_not_P, hv_inj, hInter, hℱ', hLow_eq, hTop_eq⟩ :=
    Grunbaum2003.exists_stellar_subdivision_cone_decomposition d hd P hP ℱ hℱ
  have hCone := (Grunbaum2003.stellar_cone_face_injective_disjoint_and_equiv d hd).2
    ℱ hℱ y hy_not_P v hv_inj hInter
  let ℱ_new : ℕ → Finset (Set (Fin d → ℝ)) := fun k =>
    ((Finset.univ : Finset (Fin d)).powersetCard k).image
      (fun s : Finset (Fin d) => convexHull ℝ (insert y (v '' (s : Set (Fin d)))))
  refine ⟨P', F₀, ℱ', ℱ_new, hP', hF₀, hℱ', ?_, ?_⟩
  · intro j hlt
    exact ⟨hLow_eq j hlt, (hCone.1 j.val).1, (hCone.1 j.val).2⟩
  · exact ⟨hTop_eq, hCone.2 F₀, (hCone.1 (d - 1)).2⟩
