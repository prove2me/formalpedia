-- Prove2me | solution 1 for Grunbaum2003.exists_vertex_cut_level
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:36:16.665492+00:00
-- url     : https://prove2.me/submissions/83839472-028b-409e-a31d-2f5f534500b9

import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Grunbaum2003

/-- The cutting hyperplane in Grünbaum's vertex-figure induction can be chosen strictly
between an exposed vertex and every other vertex, crossing every vertex segment internally.
This is private development for `boundary_refines_simplex_ge_two`, not a published child. -/
theorem exists_vertex_cut_level (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    ∃ v : Fin d → ℝ, IsExposed ℝ P {v} ∧
      ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
        ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v →
          l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α := by
  classical
  obtain ⟨hVfin, hFaces⟩ := polytope_face_eq_convexHull_exposed_vertices d P hP
  have hPne : P.Nonempty := by
    obtain ⟨V, _, hVne, hHull⟩ := hP.1
    rw [hHull]
    exact hVne.convexHull
  have hHull := hFaces ⟨P, IsExposed.refl P⟩
  have hHullne : (convexHull ℝ (P ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})).Nonempty := by
    rw [← hHull]
    exact hPne
  obtain ⟨v, _, hv⟩ := convexHull_nonempty_iff.mp hHullne
  obtain ⟨hvP, l, hl⟩ := mem_exposedPoints_iff_exposed_singleton.mpr hv
  let V' := {x : Fin d → ℝ | IsExposed ℝ P {x}} \ {v}
  have hV'fin : V'.Finite := hVfin.diff
  have hStrict (w : Fin d → ℝ) (hw : w ∈ V') : l w < l v := by
    have hwP : w ∈ P := (mem_exposedPoints_iff_exposed_singleton.mpr hw.1).1
    apply lt_of_le_of_ne (hl w hwP).1
    intro heq
    exact hw.2 ((hl w hwP).2 heq.ge)
  obtain ⟨α, hα, hBelow⟩ : ∃ α : ℝ, α < l v ∧ ∀ w ∈ V', l w < α := by
    by_cases hV'ne : V'.Nonempty
    · obtain ⟨w, hw, hMax⟩ := Set.exists_max_image V' l hV'fin hV'ne
      refine ⟨(l w + l v) / 2, ?_, ?_⟩
      · linarith [hStrict w hw]
      · intro u hu
        linarith [hMax u hu, hStrict w hw]
    · refine ⟨l v - 1, by linarith, ?_⟩
      intro w hw
      exact (hV'ne ⟨w, hw⟩).elim
  refine ⟨v, hv, l, α, hα, fun x hx => (hl x hx).1, ?_⟩
  intro w hw hwv
  have hwα : l w < α := hBelow w ⟨hw, hwv⟩
  refine ⟨hwα, ?_⟩
  let t : ℝ := (l v - α) / (l v - l w)
  have hDen : 0 < l v - l w := sub_pos.mpr (hwα.trans hα)
  have htPos : 0 < t := div_pos (sub_pos.mpr hα) hDen
  have htOne : t < 1 := (div_lt_one hDen).mpr (by linarith)
  refine ⟨t, htPos, htOne, ?_⟩
  have htMul : t * (l v - l w) = l v - α := div_mul_cancel₀ _ hDen.ne'
  rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul]
  nlinarith [htMul]

end Grunbaum2003


open Grunbaum2003
theorem solution (d : ℕ) (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    ∃ v : Fin d → ℝ, IsExposed ℝ P {v} ∧
      ∃ (l : StrongDual ℝ (Fin d → ℝ)) (α : ℝ),
        α < l v ∧ (∀ x ∈ P, l x ≤ l v) ∧
        ∀ w : Fin d → ℝ, IsExposed ℝ P {w} → w ≠ v →
          l w < α ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ l (AffineMap.lineMap v w t) = α :=
  Grunbaum2003.exists_vertex_cut_level d P hP
