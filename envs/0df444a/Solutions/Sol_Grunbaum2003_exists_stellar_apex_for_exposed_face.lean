-- Prove2me | solution 1 for Grunbaum2003.exists_stellar_apex_for_exposed_face
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:06:22.483448+00:00
-- url     : https://prove2.me/submissions/75d51281-7dd8-44db-a982-95ff4ceb7c2e

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped Classical

namespace Grunbaum2003

/-- An apex strictly beyond a supporting hyperplane adds no points of the old
convex set to a cone over a subset of that hyperplane. -/
theorem convexHull_insert_inter_eq_of_supporting {d : ℕ}
    {P A : Set (Fin d → ℝ)} (hP : Convex ℝ P) (hAP : A ⊆ P)
    (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ c) (hlevel : ∀ x ∈ A, φ x = c)
    (y : Fin d → ℝ) (hy : c < φ y) :
    convexHull ℝ (insert y A) ∩ P = convexHull ℝ A := by
  have hyP : y ∉ P := fun h => (not_le_of_gt hy) (hbound y h)
  have hsub : convexHull ℝ A ⊆ P := convexHull_min hAP hP
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hA : A.Nonempty
    · have hconst : ∀ z ∈ convexHull ℝ A, φ z = c := by
        exact convexHull_min hlevel ((convex_singleton c).linear_preimage φ)
      rcases hx with ⟨hx, hxP⟩
      rw [convexHull_insert hA, mem_convexJoin] at hx
      rcases hx with ⟨y', hy', z, hz, a, b, ha, hb, hab, hx⟩
      obtain rfl : y' = y := hy'
      subst x
      have hφ := hbound _ hxP
      simp only [map_add, map_smul, smul_eq_mul, hconst z hz] at hφ
      have ha0 : a = 0 := by
        apply le_antisymm _ ha
        by_contra! hapos
        nlinarith [mul_pos hapos (sub_pos.mpr hy), congrArg (fun t : ℝ => t * c) hab]
      have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hz
    · have hA0 : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
      have hxy : x = y := by simpa [hA0] using hx.1
      exact False.elim (hyP (hxy ▸ hx.2))
  · intro x hx
    exact ⟨convexHull_mono (Set.subset_insert y A) hx, hsub hx⟩

/-- The cone over selected old exposed vertices has exactly those old exposed
vertices when the apex lies strictly beyond their supporting hyperplane. -/
theorem stellarCone_old_exposed_vertices_of_supporting {d : ℕ}
    {P : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (v : Fin d → Fin d → ℝ)
    (hv : ∀ i, IsExposed ℝ P {v i})
    (φ : (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ P, φ x ≤ c) (hlevel : ∀ i, φ (v i) = c)
    (y : Fin d → ℝ) (hy : c < φ y) (s : Finset (Fin d)) :
    convexHull ℝ (insert y (v '' (s : Set (Fin d)))) ∩
      {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set (Fin d)) := by
  have hAP : v '' (s : Set (Fin d)) ⊆ P := by
    rintro _ ⟨i, _, rfl⟩
    exact (hv i).subset (Set.mem_singleton _)
  have hconv := convexHull_insert_inter_eq_of_supporting hP hAP φ c hbound
    (by rintro _ ⟨i, _, rfl⟩; exact hlevel i) y hy
  apply Set.Subset.antisymm
  · intro x hx
    have hxP := hx.2.subset (Set.mem_singleton _)
    have hxHull : x ∈ convexHull ℝ (v '' (s : Set (Fin d))) := by
      rw [← hconv]
      exact ⟨hx.1, hxP⟩
    exact extremePoints_convexHull_subset
      (inter_extremePoints_subset_extremePoints_of_subset
        (convexHull_min hAP hP) ⟨hxHull, hx.2.isExtreme.mem_extremePoints⟩)
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩), hv i⟩


end Grunbaum2003

open Grunbaum2003

/-- Every proper nonempty exposed face admits an exterior apex whose cones
over selected old vertices contain exactly those old exposed vertices. -/
theorem solution {d : ℕ}
    {P F : Set (Fin d → ℝ)} (hP : Convex ℝ P)
    (hF : IsExposed ℝ P F) (hFne : F.Nonempty) (hproper : F ≠ P)
    (v : Fin d → Fin d → ℝ)
    (hv : ∀ i, IsExposed ℝ P {v i}) (hvF : ∀ i, v i ∈ F) :
    ∃ y : Fin d → ℝ, y ∉ P ∧
      ∀ s : Finset (Fin d),
        convexHull ℝ (insert y (v '' (s : Set (Fin d)))) ∩
          {x : Fin d → ℝ | IsExposed ℝ P {x}} = v '' (s : Set (Fin d)) := by
  obtain ⟨φ, hφ⟩ := hF hFne
  obtain ⟨w, hwF⟩ := hFne
  have hw := hwF
  rw [hφ] at hw
  have hbound : ∀ x ∈ P, φ x ≤ φ w := hw.2
  have hzex : ¬ P ⊆ F := fun h => hproper (Set.Subset.antisymm hF.subset h)
  obtain ⟨z, hzP, hzF⟩ := Set.not_subset.mp hzex
  have hzw : φ z < φ w := by
    apply lt_of_le_of_ne (hbound z hzP)
    intro h
    apply hzF
    rw [hφ]
    exact ⟨hzP, fun x hx => h ▸ hbound x hx⟩
  have hlevel : ∀ i, φ (v i) = φ w := by
    intro i
    have hvi := hvF i
    rw [hφ] at hvi
    exact le_antisymm (hbound (v i) hvi.1) (hvi.2 w hw.1)
  let y := w + (w - z)
  have hy : φ w < φ y := by
    dsimp [y]
    rw [map_add, map_sub]
    linarith
  refine ⟨y, fun h => (not_le_of_gt hy) (hbound y h), fun s => ?_⟩
  exact stellarCone_old_exposed_vertices_of_supporting hP v hv φ.toLinearMap
    (φ w) hbound hlevel y hy s
