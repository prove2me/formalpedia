-- Prove2me | solution 1 for N25.GammaH25GL_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:51.773293+00:00
-- url     : https://prove2.me/submissions/1c394d1e-cf65-459e-b865-32be6f1780aa

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25_Endgame
import Theorems.Thm_N25_level25_indices
import Definitions.Def_N25

set_option autoImplicit false

open scoped MatrixGroups

open Matrix.SpecialLinearGroup

namespace N25

theorem _root_.solution : GammaH25GL.relIndex 𝒮ℒ = 150 := by
  change ((CohCarrier.GammaH 25 N25.H25).map (mapGL ℝ)).relIndex
    (mapGL (R := ℤ) ℝ).range = 150
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
    Subgroup.relIndex_top_right]
  exact N25.level25_indices.1

end N25
