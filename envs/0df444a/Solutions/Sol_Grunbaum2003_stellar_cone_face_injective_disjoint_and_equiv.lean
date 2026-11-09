-- Prove2me | solution 1 for Grunbaum2003.stellar_cone_face_injective_disjoint_and_equiv
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:44:37.837334+00:00
-- url     : https://prove2.me/submissions/26af1696-fe55-444d-8fb6-a1a8b0563c37

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_g_theorem_necessity_stacked_and_simplicial_facets
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped Classical

open Grunbaum2003

/-- For a stellar apex `y : Fin d → ℝ`, facet vertex map `v : Fin d → Fin d → ℝ`, and subset
`s : Finset (Fin d)`, the cone face over `v '' s` with apex `y` is
`convexHull ℝ (insert y (v '' (s : Set (Fin d))))`. -/
def stellarConeFace {d : ℕ} (y : Fin d → ℝ) (v : Fin d → Fin d → ℝ) (s : Finset (Fin d)) :
    Set (Fin d → ℝ) :=
  convexHull ℝ (insert y (v '' (s : Set (Fin d))))

/-- Every stellar cone face `stellarConeFace y v s` contains the apex `y`. -/
lemma mem_stellarConeFace_self {d : ℕ} (y : Fin d → ℝ) (v : Fin d → Fin d → ℝ)
    (s : Finset (Fin d)) :
    y ∈ stellarConeFace y v s :=
  subset_convexHull ℝ (insert y (v '' (s : Set (Fin d)))) (Set.mem_insert y _)

/-- If `stellarConeFace y v s ∩ V = v '' s` for all `s : Finset (Fin d)` and `v` is injective,
then `stellarConeFace y v` is injective on `Finset (Fin d)`. -/
lemma stellarConeFace_injective {d : ℕ} (y : Fin d → ℝ) (v : Fin d → Fin d → ℝ)
    (hv_inj : Function.Injective v)
    (V : Set (Fin d → ℝ))
    (hInter : ∀ s : Finset (Fin d), stellarConeFace y v s ∩ V = v '' (s : Set (Fin d))) :
    Function.Injective (stellarConeFace y v) := by
  intro s₁ s₂ hEq
  have h1 : stellarConeFace y v s₁ ∩ V = stellarConeFace y v s₂ ∩ V := by rw [hEq]
  rw [hInter s₁, hInter s₂, Set.image_eq_image hv_inj] at h1
  exact Finset.coe_inj.mp h1

/-- When `y ∉ P` and `stellarConeFace y v` is injective, the image finsets
`ℱ_new k := ((Finset.univ : Finset (Fin d)).powersetCard k).image (stellarConeFace y v)`
are disjoint from every `k`-face finset `ℱ k` of `P` (and from `(ℱ (d - 1)).erase F₀`),
and each `ℱ_new k` is in bijection with `(Finset.univ : Finset (Fin d)).powersetCard k`. -/
lemma stellarConeFace_disjoint_and_equiv {d : ℕ}
    {P : Set (Fin d → ℝ)}
    (ℱ : ℕ → Finset (Set (Fin d → ℝ)))
    (hℱ : ∀ k : ℕ, (ℱ k : Set (Set (Fin d → ℝ))) =
      {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
      (ℱ k).card = faceCount P k)
    (y : Fin d → ℝ) (hy_not_P : y ∉ P)
    (v : Fin d → Fin d → ℝ)
    (hInj : Function.Injective (stellarConeFace y v)) :
    let ℱ_new : ℕ → Finset (Set (Fin d → ℝ)) := fun k =>
      ((Finset.univ : Finset (Fin d)).powersetCard k).image (stellarConeFace y v)
    (∀ k : ℕ,
      Disjoint (ℱ k) (ℱ_new k) ∧
      Nonempty (ℱ_new k ≃ (Finset.univ : Finset (Fin d)).powersetCard k)) ∧
    (∀ F₀ : Set (Fin d → ℝ),
      Disjoint ((ℱ (d - 1)).erase F₀) (ℱ_new (d - 1))) := by
  intro ℱ_new
  have hDisj : ∀ k : ℕ, Disjoint (ℱ k) (ℱ_new k) := by
    intro k
    rw [Finset.disjoint_left]
    intro F hF_old hF_new
    have hF_mem : F ∈ (ℱ k : Set (Set (Fin d → ℝ))) := hF_old
    rw [(hℱ k).1] at hF_mem
    have hF_sub : F ⊆ P := hF_mem.2.1.subset
    rw [Finset.mem_image] at hF_new
    rcases hF_new with ⟨s, _, rfl⟩
    exact hy_not_P (hF_sub (mem_stellarConeFace_self y v s))
  have hEquiv : ∀ k : ℕ,
      Nonempty (ℱ_new k ≃ (Finset.univ : Finset (Fin d)).powersetCard k) := by
    intro k
    have hCard : (ℱ_new k).card = ((Finset.univ : Finset (Fin d)).powersetCard k).card :=
      Finset.card_image_of_injective _ hInj
    refine ⟨Fintype.equivOfCardEq ?_⟩
    simp only [Fintype.card_coe, hCard]
  refine ⟨fun k => ⟨hDisj k, hEquiv k⟩, fun F₀ => ?_⟩
  exact Disjoint.mono_left (Finset.erase_subset F₀ (ℱ (d - 1))) (hDisj (d - 1))

theorem solution (d : ℕ) (hd : 4 ≤ d) :
    (∀ {P : Set (Fin d → ℝ)}, IsSimplicialDPolytope P →
      ∀ (ℱ : ℕ → Finset (Set (Fin d → ℝ))),
        (∀ k : ℕ, (ℱ k : Set (Set (Fin d → ℝ))) =
          {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
            Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
          (ℱ k).card = faceCount P k) →
        ∀ (F₀ : Set (Fin d → ℝ)), F₀ ∈ ℱ (d - 1) →
          ∃ v : Fin d → Fin d → ℝ,
            AffineIndependent ℝ v ∧
            Function.Injective v ∧
            (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
            F₀ = convexHull ℝ (Set.range v) ∧
            F₀ ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v) ∧
    (∀ {P : Set (Fin d → ℝ)}
      (ℱ : ℕ → Finset (Set (Fin d → ℝ))),
      (∀ k : ℕ, (ℱ k : Set (Set (Fin d → ℝ))) =
        {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = k} ∧
        (ℱ k).card = faceCount P k) →
      ∀ (y : Fin d → ℝ), y ∉ P →
      ∀ (v : Fin d → Fin d → ℝ), Function.Injective v →
      (∀ s : Finset (Fin d),
        convexHull ℝ (insert y (v '' (s : Set (Fin d)))) ∩
          {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set (Fin d))) →
      let ℱ_new : ℕ → Finset (Set (Fin d → ℝ)) := fun k =>
        ((Finset.univ : Finset (Fin d)).powersetCard k).image
          (fun s : Finset (Fin d) => convexHull ℝ (insert y (v '' (s : Set (Fin d)))))
      (∀ k : ℕ,
        Disjoint (ℱ k) (ℱ_new k) ∧
        Nonempty (ℱ_new k ≃ (Finset.univ : Finset (Fin d)).powersetCard k)) ∧
      (∀ F₀ : Set (Fin d → ℝ),
        Disjoint ((ℱ (d - 1)).erase F₀) (ℱ_new (d - 1)))) := by
  refine ⟨?_, ?_⟩
  · intro P hP ℱ hℱ F₀ hF₀
    have hF₀_mem : F₀ ∈ (ℱ (d - 1) : Set (Set (Fin d → ℝ))) := hF₀
    rw [(hℱ (d - 1)).1] at hF₀_mem
    obtain ⟨hne, hexp, hdim⟩ := hF₀_mem
    have hdim' : Module.finrank ℝ (affineSpan ℝ F₀).direction + 1 = d := by omega
    obtain ⟨v, hAff, hInj, hVert, hHull, hInter, _, _, _⟩ :=
      Grunbaum2003.g_theorem_necessity_stacked_and_simplicial_facets.1 hP F₀ hne hexp hdim'
    exact ⟨v, hAff, hInj, hVert, hHull, hInter⟩
  · intro P ℱ hℱ y hy_not_P v hv_inj hInter
    have hInj : Function.Injective (stellarConeFace y v) :=
      stellarConeFace_injective y v hv_inj {x : Fin d → ℝ | IsExposed ℝ P {x}} hInter
    exact stellarConeFace_disjoint_and_equiv ℱ hℱ y hy_not_P v hInj
