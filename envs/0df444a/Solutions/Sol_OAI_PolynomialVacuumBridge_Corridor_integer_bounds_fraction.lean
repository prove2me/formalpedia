-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.integer_bounds_fraction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:57:53.982856+00:00
-- url     : https://prove2.me/submissions/333ac95b-d7d7-435c-aabf-914afd05a42f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Convexity.lean:L49-L65
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.integer_bounds_fraction. The node keeps its source
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

theorem integer_bounds_fraction (lo hi n : ℤ) (a : ℝ) (ha : 0 < a) (ha' : a < 1) :
    ((lo : ℝ) < (n : ℝ)+a ∧ (n : ℝ)+a < (hi : ℝ)) ↔ lo ≤ n ∧ n < hi := by
  constructor
  · rintro ⟨hl,hh⟩
    constructor
    · by_contra h
      have h' : n+1 ≤ lo := by omega
      have : (n : ℝ)+1 ≤ (lo : ℝ) := by exact_mod_cast h'
      linarith
    · by_contra h
      have h' : hi ≤ n := by omega
      have : (hi : ℝ) ≤ (n : ℝ) := by exact_mod_cast h'
      linarith
  · rintro ⟨hl,hh⟩
    have hl' : (lo : ℝ) ≤ (n : ℝ) := by exact_mod_cast hl
    have hh' : (n : ℝ)+1 ≤ (hi : ℝ) := by exact_mod_cast (show n+1 ≤ hi by omega)
    constructor <;> linarith

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.integer_bounds_fraction := @_root_.OAI.PolynomialVacuumBridge.Corridor.integer_bounds_fraction
