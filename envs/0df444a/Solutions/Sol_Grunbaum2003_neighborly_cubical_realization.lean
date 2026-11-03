-- Prove2me | solution 1 for Grunbaum2003.neighborly_cubical_realization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:28:38.986742+00:00
-- url     : https://prove2.me/submissions/3bf73c72-16e0-4bec-a8d3-2d50b3212acc

import Definitions.Def_Grunbaum2003_IsCubicalDPolytope
import Definitions.Def_Grunbaum2003_SkeletonFace
import Definitions.Def_Grunbaum2003_standardCube
import Theorems.Thm_Grunbaum2003_skeletonFace_zero_orderIso_of_exposed_vertices_equiv
import Theorems.Thm_Grunbaum2003_joswig_ziegler_cubical_realization_and_vertex_equiv
import Mathlib.Tactic

set_option autoImplicit false

namespace Grunbaum2003

/-- Joswig–Ziegler neighborly cubical realization (Grünbaum 2003, §4.9, p. 69b):
for every `n > d ≥ 2`, there exists a cubical `d`-polytope `P` whose `(⌊d / 2⌋ - 1)`-skeleton
is order-isomorphic to that of the standard `n`-cube. -/
theorem neighborly_cubical_realization_sol (n d : ℕ) (hd : 2 ≤ d) (hnd : d < n) :
    ∃ P : Set (Fin d → ℝ), IsCubicalDPolytope P ∧
      Nonempty (SkeletonFace P (d / 2 - 1) ≃o
        SkeletonFace (standardCube n) (d / 2 - 1)) := by
  obtain ⟨hLow, hHigh⟩ :=
    joswig_ziegler_cubical_realization_and_vertex_equiv n d hd hnd
  by_cases hd3 : d ≤ 3
  · obtain ⟨P, hCub, ⟨e⟩⟩ := hLow hd3
    have hk0 : d / 2 - 1 = 0 := by omega
    rw [hk0]
    exact ⟨P, hCub,
      skeletonFace_zero_orderIso_of_exposed_vertices_equiv d n P (standardCube n) e⟩
  · have hd4 : 4 ≤ d := by omega
    exact hHigh hd4

end Grunbaum2003

theorem solution (n d : ℕ) (hd : 2 ≤ d) (hnd : d < n) :
    ∃ P : Set (Fin d → ℝ), Grunbaum2003.IsCubicalDPolytope P ∧
      Nonempty (Grunbaum2003.SkeletonFace P (d / 2 - 1) ≃o
        Grunbaum2003.SkeletonFace (Grunbaum2003.standardCube n) (d / 2 - 1)) :=
  Grunbaum2003.neighborly_cubical_realization_sol n d hd hnd
