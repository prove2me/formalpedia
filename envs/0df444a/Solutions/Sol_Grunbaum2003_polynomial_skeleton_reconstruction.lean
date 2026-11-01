-- Prove2me | solution 1 for Grunbaum2003.polynomial_skeleton_reconstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:26:57.024123+00:00
-- url     : https://prove2.me/submissions/6614ef1d-5cf4-413d-b5eb-d36449d8e8d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_containmentBitBlock
import Definitions.Def_Grunbaum2003_ContainmentPolyTime
import Definitions.Def_Grunbaum2003_reconstructionIncidenceCode
import Definitions.Def_Grunbaum2003_HasReconstructionFaceRows
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_exists_polyTime_facet_incidence_reconstructor
import Mathlib.Analysis.Convex.Exposed

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), §12.4 (“Algorithmic aspects”, p. 234a): there is a uniform
polynomial-time algorithm that reconstructs all vertex-facet incidence rows of a
`d`-polytope (`d ≥ 3`) from its `(d - 2)`-skeleton vertex-face incidence rows. -/
theorem polynomial_skeleton_reconstruction_sol :
    ∃ algorithm : List Bool → List Bool, ContainmentPolyTime algorithm ∧
      ∀ (d n : ℕ), 3 ≤ d →
        ∀ (P : Set (Fin d → ℝ)), IsDPolytope P →
          ∀ (v : Fin n → Fin d → ℝ), Function.Injective v →
            Set.range v = {x | IsExposed ℝ P {x}} →
            ∀ rows : List (Finset (Fin n)),
              HasReconstructionFaceRows P v (Set.Iic (d - 2)) rows →
              ∃ facets : List (Finset (Fin n)),
                HasReconstructionFaceRows P v {d - 1} facets ∧
                algorithm (reconstructionIncidenceCode d n rows) =
                  reconstructionIncidenceCode d n facets := by
  obtain ⟨algorithm, hPoly, hRec⟩ := exists_polyTime_facet_incidence_reconstructor
  refine ⟨algorithm, hPoly, ?_⟩
  intro d n hd P hP v hv_inj hv_range rows hrows
  exact hRec d n hd P hP
    (polytope_face_eq_convexHull_exposed_vertices d P hP) v hv_inj hv_range rows hrows

end Grunbaum2003

theorem solution :
    ∃ algorithm : List Bool → List Bool, Grunbaum2003.ContainmentPolyTime algorithm ∧
      ∀ (d n : ℕ), 3 ≤ d →
        ∀ (P : Set (Fin d → ℝ)), Grunbaum2003.IsDPolytope P →
          ∀ (v : Fin n → Fin d → ℝ), Function.Injective v →
            Set.range v = {x | IsExposed ℝ P {x}} →
            ∀ rows : List (Finset (Fin n)),
              Grunbaum2003.HasReconstructionFaceRows P v (Set.Iic (d - 2)) rows →
              ∃ facets : List (Finset (Fin n)),
                Grunbaum2003.HasReconstructionFaceRows P v {d - 1} facets ∧
                algorithm (Grunbaum2003.reconstructionIncidenceCode d n rows) =
                  Grunbaum2003.reconstructionIncidenceCode d n facets :=
  Grunbaum2003.polynomial_skeleton_reconstruction_sol
