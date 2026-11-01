-- Prove2me | solution 1 for Grunbaum2003.polytopeFace_trichotomy_codim_two
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:17:18.45288+00:00
-- url     : https://prove2.me/submissions/09e7d5db-fd7f-42b6-92d2-d02c31a62482

import Definitions.Def_Grunbaum2003_PolytopeFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

set_option autoImplicit false

namespace Grunbaum2003

/-- Every face of a `d`-polytope (`d > 0`) either lies in the `(d - 2)`-skeleton,
equals the improper face `P` itself, or is a facet of dimension `d - 1`. -/
theorem polytopeFace_trichotomy_codim_two (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (F : PolytopeFace P) :
    (F.val = ∅ ∨ Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ d - 2) ∨
      F.val = P ∨
      (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1) := by
  rcases F.val.eq_empty_or_nonempty with hEmpty | hFne
  · exact Or.inl (Or.inl hEmpty)
  · have hle : Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ d := by
      have h1 := Submodule.finrank_le (affineSpan ℝ F.val).direction
      simpa [Module.finrank_fin_fun] using h1
    rcases ( by omega :
        Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ d - 2 ∨
        Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1 ∨
        Module.finrank ℝ (affineSpan ℝ F.val).direction = d ) with h2 | h1 | h0
    · exact Or.inl (Or.inr h2)
    · exact Or.inr (Or.inr ⟨hFne, h1⟩)
    · refine Or.inr (Or.inl ?_)
      obtain ⟨l, hl⟩ := F.2 hFne
      have hdir_top : (affineSpan ℝ F.val).direction = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [h0, Module.finrank_fin_fun]
      have hker_top : (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ LinearMap.ker l.toLinearMap := by
        rw [← hdir_top, direction_affineSpan, vectorSpan_def, Submodule.span_le]
        rintro v ⟨a, ha, b, hb, rfl⟩
        have haP : a ∈ P := by rw [hl] at ha; exact ha.1
        have hbP : b ∈ P := by rw [hl] at hb; exact hb.1
        have hamax : ∀ y ∈ P, l y ≤ l a := by rw [hl] at ha; exact ha.2
        have hbmax : ∀ y ∈ P, l y ≤ l b := by rw [hl] at hb; exact hb.2
        have hab : l a = l b := le_antisymm (hbmax a haP) (hamax b hbP)
        simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
          vsub_eq_sub, map_sub, hab, sub_self]
      have hl_eq : ∀ x y : Fin d → ℝ, l x = l y := by
        intro x y
        have hxy : x - y ∈ LinearMap.ker l.toLinearMap := hker_top trivial
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sub_eq_zero] at hxy
        exact hxy
      rw [hl]
      ext x
      simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro _ y _
      exact le_of_eq (hl_eq y x)

end Grunbaum2003

theorem solution (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (F : Grunbaum2003.PolytopeFace P) :
    (F.val = ∅ ∨ Module.finrank ℝ (affineSpan ℝ F.val).direction ≤ d - 2) ∨
      F.val = P ∨
      (F.val.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F.val).direction = d - 1) :=
  Grunbaum2003.polytopeFace_trichotomy_codim_two d hd P F
