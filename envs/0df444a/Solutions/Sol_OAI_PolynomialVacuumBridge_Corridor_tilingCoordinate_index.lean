-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.tilingCoordinate_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:56:26.738091+00:00
-- url     : https://prove2.me/submissions/2adb8a5e-be16-45af-a0c2-a4a7f1c5c40b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Convexity.lean:L17-L47
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.tilingCoordinate_index. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity

-- ---- from OAI.Combinatorics.HoneycombCorridor.Convexity ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem tilingCoordinate_index (v : Vertex) (k : Fin 3) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      tilingCoordinate k (position v) = (boxIndex v k : ℝ) + a := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  cases v with
  | up i j =>
    fin_cases k
    · refine ⟨1/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
    · refine ⟨1/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring
    · refine ⟨2/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring
  | down i j =>
    fin_cases k
    · refine ⟨2/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
    · refine ⟨2/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring
    · refine ⟨1/3,by norm_num,by norm_num,?_⟩
      simp [tilingCoordinate,position,boxIndex]
      field_simp
      ring

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.tilingCoordinate_index := @_root_.OAI.PolynomialVacuumBridge.Corridor.tilingCoordinate_index
