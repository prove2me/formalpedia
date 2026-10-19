-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.upperCut_convex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:25:56.62377+00:00
-- url     : https://prove2.me/submissions/89652db4-1f94-493d-be36-3326aed4788b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/ConvexCuts.lean:L30-L52
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.upperCut_convex. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_integer_bounds_fraction
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_tilingCoordinate_index

-- ---- from OAI.Combinatorics.HoneycombCorridor.Convexity ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem admissiblyConvex_box (D : Finset Vertex) (hD : AdmissiblyConvex D) :
    ∃ lo hi : Fin 3 → ℤ, ∀ v, v ∈ D ↔ BoxMem lo hi v := by
  obtain ⟨lo,hi,h⟩ := hD
  refine ⟨lo,hi,fun v => ?_⟩
  rw [h]
  apply forall_congr'
  intro k
  obtain ⟨a,ha,ha',he⟩ := tilingCoordinate_index v k
  rw [he]
  exact integer_bounds_fraction _ _ _ _ ha ha'

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.ConvexCuts ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem admissiblyConvex_of_box (D : Finset Vertex) (lo hi : Fin 3 → ℤ)
    (h : ∀ v, v ∈ D ↔ BoxMem lo hi v) : AdmissiblyConvex D := by
  refine ⟨lo,hi,fun v => ?_⟩
  rw [h]
  apply forall_congr'
  intro k
  obtain ⟨a,ha,ha',he⟩ := tilingCoordinate_index v k
  rw [he]
  exact (integer_bounds_fraction _ _ _ _ ha ha').symm

theorem upperCut_convex (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (k : Fin 3) (A : ℤ) : AdmissiblyConvex (upperCut D k A) := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  apply admissiblyConvex_of_box _ lo (fun l => if l = k then min (hi l) A else hi l)
  intro v
  simp only [mem_upperCut,hbox,BoxMem]
  constructor
  · rintro ⟨hv,hA⟩ l
    by_cases hl : l = k
    · subst l; simpa only [ite_true,lt_min_iff] using ⟨(hv k).1,(hv k).2,hA⟩
    · simpa only [hl,ite_false] using hv l
  · intro hv
    constructor
    · intro l
      by_cases hl : l = k
      · subst l
        have hh := hv k
        simp only [ite_true,lt_min_iff] at hh
        exact ⟨hh.1,hh.2.1⟩
      · simpa only [hl,ite_false] using hv l
    · have hh := hv k
      simp only [ite_true,lt_min_iff] at hh
      exact hh.2.2

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.upperCut_convex := @_root_.OAI.PolynomialVacuumBridge.Corridor.upperCut_convex
