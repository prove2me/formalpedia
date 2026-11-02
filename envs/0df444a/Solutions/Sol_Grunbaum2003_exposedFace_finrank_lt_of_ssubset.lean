-- Prove2me | solution 1 for Grunbaum2003.exposedFace_finrank_lt_of_ssubset
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:01:30.830148+00:00
-- url     : https://prove2.me/submissions/03aef08c-d3a3-449f-a2d6-03f0eb6c5849

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

/-- A nonempty proper exposed face has strictly smaller affine dimension
than any intermediate set. No compactness or convexity is required. -/
theorem exposedFace_finrank_lt_of_ssubset {d : ℕ}
    {P F G : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F)
    (hFne : F.Nonempty) (hFG : F ⊂ G) (hGP : G ⊆ P) :
    Module.finrank ℝ (affineSpan ℝ F).direction <
      Module.finrank ℝ (affineSpan ℝ G).direction := by
  obtain ⟨l, hl⟩ := hF hFne
  have hker : (affineSpan ℝ F).direction ≤ LinearMap.ker l.toLinearMap := by
    rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro v ⟨a, ha, b, hb, rfl⟩
    have ha' := ha
    have hb' := hb
    rw [hl] at ha' hb'
    have hab : l a = l b := le_antisymm (hb'.2 a ha'.1) (ha'.2 b hb'.1)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      vsub_eq_sub, map_sub, hab, sub_self]
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne (AffineSubspace.direction_le (affineSpan_mono ℝ hFG.le))
  intro hdir
  obtain ⟨x, hx⟩ := hFne
  obtain ⟨y, hyG, hyF⟩ := Set.exists_of_ssubset hFG
  have hyx : y -ᵥ x ∈ (affineSpan ℝ G).direction :=
    AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ G hyG) (subset_affineSpan ℝ G (hFG.le hx))
  rw [← hdir] at hyx
  have hlyx := hker hyx
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    vsub_eq_sub, map_sub, sub_eq_zero] at hlyx
  apply hyF
  rw [hl]
  refine ⟨hGP hyG, ?_⟩
  have hx' := hx
  rw [hl] at hx'
  intro z hz
  rw [hlyx]
  exact hx'.2 z hz

end Grunbaum2003

theorem solution {d : ℕ}
    {P F G : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F)
    (hFne : F.Nonempty) (hFG : F ⊂ G) (hGP : G ⊆ P) :
    Module.finrank ℝ (affineSpan ℝ F).direction <
      Module.finrank ℝ (affineSpan ℝ G).direction :=
  Grunbaum2003.exposedFace_finrank_lt_of_ssubset hF hFne hFG hGP
