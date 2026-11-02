-- Prove2me | solution 1 for Grunbaum2003.boundary_carrier_frontier_and_homeomorphism
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:31:12.928077+00:00
-- url     : https://prove2.me/submissions/dc6df19a-6cfb-4dbb-a42a-78b2db49c790

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_boundaryFaces
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

namespace Grunbaum2003

private theorem proper_exposed_disjoint_interior {d : ℕ}
    {P F : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F) (hFP : F ≠ P) :
    Disjoint F (interior P) := by
  apply Set.disjoint_left.mpr
  intro x hxF hxint
  obtain ⟨l, hl⟩ := hF ⟨x, hxF⟩
  by_cases hlzero : l = 0
  · apply hFP
    rw [hl, hlzero]
    ext y
    simp only [Set.mem_setOf_eq, ContinuousLinearMap.zero_apply, le_refl, implies_true,
      and_true]
  · have hxmax : ∀ y ∈ P, l y ≤ l x := by
      rw [hl] at hxF
      exact hxF.2
    have hSub : l '' interior P ⊆ Set.Iic (l x) := by
      rintro _ ⟨y, hy, rfl⟩
      exact hxmax y (interior_subset hy)
    have hopen : IsOpen (l '' interior P) := l.isOpenMap_of_ne_zero hlzero (interior P) isOpen_interior
    have hx : l x ∈ interior (Set.Iic (l x)) :=
      interior_maximal hSub hopen (Set.mem_image_of_mem l hxint)
    simpa only [interior_Iic, Set.mem_Iio, lt_self_iff_false] using hx

/-- The exposed-face boundary carrier of a closed convex body with nonempty
interior agrees with its topological frontier. -/
theorem boundary_carrier_eq_frontier_of_convex {d : ℕ}
    (P : Set (Fin d → ℝ)) (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hint : (interior P).Nonempty) :
    ⋃₀ boundaryFaces P = frontier P := by
  ext x
  rw [hclosed.frontier_eq]
  constructor
  · rintro ⟨F, ⟨hF, hFP⟩, hxF⟩
    exact ⟨hF.subset hxF, fun hx =>
      Set.disjoint_left.mp (proper_exposed_disjoint_interior hF hFP) hxF hx⟩
  · rintro ⟨hxP, hxint⟩
    obtain ⟨l, hlne, hlmax⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hconv hxint hint
    let F := l.toExposed P
    have hxF : x ∈ F := ⟨hxP, hlmax⟩
    have hFP : F ≠ P := by
      intro heq
      obtain ⟨y, hyint⟩ := hint
      have hyF : y ∈ F := by rw [heq]; exact interior_subset hyint
      have hSub : l '' interior P ⊆ Set.Iic (l y) := by
        rintro _ ⟨z, hz, rfl⟩
        exact hyF.2 z (interior_subset hz)
      have hopen : IsOpen (l '' interior P) := l.isOpenMap_of_ne_zero hlne (interior P) isOpen_interior
      have hy : l y ∈ interior (Set.Iic (l y)) :=
        interior_maximal hSub hopen (Set.mem_image_of_mem l hyint)
      simpa only [interior_Iic, Set.mem_Iio, lt_self_iff_false] using hy
    exact ⟨F, ⟨ContinuousLinearMap.toExposed.isExposed, hFP⟩, hxF⟩

theorem boundary_carrier_eq_frontier {d : ℕ}
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    ⋃₀ boundaryFaces P = frontier P := by
  obtain ⟨⟨V, hVfin, hVne, hPV⟩, hspan⟩ := hP
  have hc : Convex ℝ P := by rw [hPV]; exact convex_convexHull ℝ V
  have hcompact : IsCompact P := hPV ▸ hVfin.isCompact_convexHull ℝ
  apply boundary_carrier_eq_frontier_of_convex P hc hcompact.isClosed
  exact hc.interior_nonempty_iff_affineSpan_eq_top.mpr hspan

/-- This is the carrier part of boundary refinement. The additional requirement
that face preimages form subcomplexes is deliberately not asserted here. -/
theorem boundary_carriers_homeomorphic {d : ℕ}
    (P Q : Set (Fin d → ℝ)) (hP : IsDPolytope P) (hQ : IsDPolytope Q) :
    Nonempty ((⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces Q)) := by
  have props : ∀ R : Set (Fin d → ℝ), IsDPolytope R →
      Convex ℝ R ∧ (interior R).Nonempty ∧ Bornology.IsVonNBounded ℝ R := by
    rintro R ⟨⟨V, hVfin, hVne, hRV⟩, hspan⟩
    have hc : Convex ℝ R := by rw [hRV]; exact convex_convexHull ℝ V
    have hcomp : IsCompact R := hRV ▸ hVfin.isCompact_convexHull ℝ
    exact ⟨hc, hc.interior_nonempty_iff_affineSpan_eq_top.mpr hspan,
      NormedSpace.isVonNBounded_of_isBounded _ hcomp.isBounded⟩
  obtain ⟨hcP, hiP, hbP⟩ := props P hP
  obtain ⟨hcQ, hiQ, hbQ⟩ := props Q hQ
  obtain ⟨e, _, _, he⟩ := exists_homeomorph_image_eq hcP hiP hbP hcQ hiQ hbQ
  rw [boundary_carrier_eq_frontier P hP, boundary_carrier_eq_frontier Q hQ]
  exact ⟨(e.image (frontier P)).trans (Homeomorph.setCongr he)⟩

end Grunbaum2003


open Grunbaum2003
theorem solution (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    (⋃₀ boundaryFaces P = frontier P) ∧
      ∀ Q : Set (Fin d → ℝ), IsDPolytope Q →
        Nonempty ((⋃₀ boundaryFaces P) ≃ₜ (⋃₀ boundaryFaces Q)) :=
  ⟨boundary_carrier_eq_frontier P hP, fun Q hQ => boundary_carriers_homeomorphic P Q hP hQ⟩
