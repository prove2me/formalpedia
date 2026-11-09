-- Prove2me | solution 1 for Grunbaum2003.polytope_kFaces_finite_and_stellar_subdivision_card
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:24:05.516026+00:00
-- url     : https://prove2.me/submissions/99a89371-ff94-40cd-bea6-81dd96c6c8b2

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped Classical

open Grunbaum2003

/-- For any `d`-polytope `P`, the set of all exposed faces `{F | IsExposed ℝ P F}` is finite. -/
lemma exposedFaces_finite {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) :
    {F : Set (Fin d → ℝ) | IsExposed ℝ P F}.Finite := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP
  let V_set : Set (Fin d → ℝ) := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  have hV_fin : V_set.Finite := hHull.1
  have hPow_fin : (Set.powerset V_set).Finite := hV_fin.powerset
  have hImg_fin : ((fun S : Set (Fin d → ℝ) => convexHull ℝ S) '' Set.powerset V_set).Finite :=
    hPow_fin.image _
  refine hImg_fin.subset ?_
  intro F hF
  refine ⟨F ∩ V_set, Set.inter_subset_right, ?_⟩
  exact (hHull.2 ⟨F, hF⟩).symm

/-- For any `d`-polytope `P` and dimension `k : ℕ`, the set of `k`-dimensional exposed faces of `P`
is finite, and its `toFinset` cardinality equals `faceCount P k`. -/
lemma kFaces_finite_and_card_eq_faceCount {d : ℕ} {P : Set (Fin d → ℝ)} (hP : IsDPolytope P)
    (k : ℕ) :
    ∃ (ℱ : Finset (Set (Fin d → ℝ))),
      (ℱ : Set (Set (Fin d → ℝ))) =
        {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
      ℱ.card = faceCount P k := by
  have hFin_all := exposedFaces_finite hP
  let S_k : Set (Set (Fin d → ℝ)) :=
    {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = k}
  have hFin_k : S_k.Finite := hFin_all.subset (fun _ hF => hF.2.1)
  refine ⟨hFin_k.toFinset, hFin_k.coe_toFinset, ?_⟩
  unfold faceCount
  change hFin_k.toFinset.card = S_k.ncard
  exact (Set.ncard_eq_toFinset_card S_k hFin_k).symm

/-- Cardinality of a stellar subdivision's `j`-face and `(d - 1)`-face sets when new `j`-faces
correspond bijectively to `j`-element subsets of `Fin d` and the subdivided facet `F₀` is replaced
by `d` facets corresponding bijectively to `(d - 1)`-element subsets of `Fin d`. -/
lemma stellar_subdivision_finset_card_relations {α : Type*} (d : ℕ) (hd : 1 ≤ d) :
    (∀ (j : ℕ) (ℱ_old ℱ_new : Finset α),
      Disjoint ℱ_old ℱ_new →
      Nonempty (ℱ_new ≃ (Finset.univ : Finset (Fin d)).powersetCard j) →
      (ℱ_old ∪ ℱ_new).card = ℱ_old.card + Nat.choose d j) ∧
    (∀ (ℱ_old ℱ_new : Finset α) (F₀ : α),
      F₀ ∈ ℱ_old →
      Disjoint (ℱ_old.erase F₀) ℱ_new →
      Nonempty (ℱ_new ≃ (Finset.univ : Finset (Fin d)).powersetCard (d - 1)) →
      ((ℱ_old.erase F₀) ∪ ℱ_new).card = ℱ_old.card + (d - 1)) := by
  refine ⟨?_, ?_⟩
  · intro j ℱ_old ℱ_new hDisj ⟨e⟩
    rw [Finset.card_union_of_disjoint hDisj]
    have hcard_new : ℱ_new.card = Nat.choose d j := by
      have h1 := Fintype.card_congr e
      simp only [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h1
      exact h1
    rw [hcard_new]
  · intro ℱ_old ℱ_new F₀ hF₀ hDisj ⟨e⟩
    rw [Finset.card_union_of_disjoint hDisj]
    have hcard_new : ℱ_new.card = d := by
      have h1 := Fintype.card_congr e
      simp only [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h1
      have hchoose : Nat.choose d (d - 1) = d := by
        have hsub : d - (d - 1) = 1 := by omega
        rw [← Nat.choose_symm (by omega : d - 1 ≤ d), hsub, Nat.choose_one_right]
      omega
    have hpos : 1 ≤ ℱ_old.card := Finset.card_pos.2 ⟨F₀, hF₀⟩
    have herase : (ℱ_old.erase F₀).card = ℱ_old.card - 1 := Finset.card_erase_of_mem hF₀
    omega

theorem solution (d : ℕ) (hd : 1 ≤ d) :
    (∀ {P : Set (Fin d → ℝ)}, IsDPolytope P → ∀ (k : ℕ),
      ∃ (ℱ : Finset (Set (Fin d → ℝ))),
        (ℱ : Set (Set (Fin d → ℝ))) =
          {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
            Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
        ℱ.card = faceCount P k) ∧
    (∀ {P P' : Set (Fin d → ℝ)}
      (ℱ ℱ' ℱ_new : ℕ → Finset (Set (Fin d → ℝ))),
      (∀ k : ℕ, (ℱ k).card = faceCount P k) →
      (∀ k : ℕ, (ℱ' k).card = faceCount P' k) →
      (∀ j : Fin d, j.val + 1 < d →
        ℱ' j.val = ℱ j.val ∪ ℱ_new j.val ∧
        Disjoint (ℱ j.val) (ℱ_new j.val) ∧
        Nonempty (ℱ_new j.val ≃ (Finset.univ : Finset (Fin d)).powersetCard j.val)) →
      ∀ (F₀ : Set (Fin d → ℝ)), F₀ ∈ ℱ (d - 1) →
      (ℱ' (d - 1) = (ℱ (d - 1)).erase F₀ ∪ ℱ_new (d - 1) ∧
        Disjoint ((ℱ (d - 1)).erase F₀) (ℱ_new (d - 1)) ∧
        Nonempty (ℱ_new (d - 1) ≃ (Finset.univ : Finset (Fin d)).powersetCard (d - 1))) →
      (∀ j : Fin d, j.val + 1 < d → faceCount P' j.val = faceCount P j.val + Nat.choose d j.val) ∧
      faceCount P' (d - 1) = faceCount P (d - 1) + (d - 1)) := by
  refine ⟨fun hP k => kFaces_finite_and_card_eq_faceCount hP k, ?_⟩
  intro P P' ℱ ℱ' ℱ_new hCard hCard' hLow F₀ hF₀ hTop
  have hRel := stellar_subdivision_finset_card_relations (α := Set (Fin d → ℝ)) d hd
  refine ⟨?_, ?_⟩
  · intro j hlt
    obtain ⟨hEq, hDisj, hEquiv⟩ := hLow j hlt
    rw [← hCard' j.val, ← hCard j.val, hEq]
    exact hRel.1 j.val (ℱ j.val) (ℱ_new j.val) hDisj hEquiv
  · obtain ⟨hEq, hDisj, hEquiv⟩ := hTop
    rw [← hCard' (d - 1), ← hCard (d - 1), hEq]
    exact hRel.2 (ℱ (d - 1)) (ℱ_new (d - 1)) F₀ hF₀ hDisj hEquiv
