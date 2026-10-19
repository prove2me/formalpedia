-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.vertexWindow_convex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:39:01.117145+00:00
-- url     : https://prove2.me/submissions/ca633024-96fd-49dc-8dea-acdf88c9a7e2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/StripWindows.lean:L66-L85
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.vertexWindow_convex. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripDecay
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Reflection
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralMass
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripWindows
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_integer_bounds_fraction
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_tilingCoordinate_index

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

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.StripDecay ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem strip_index_bounds (h : ℕ) (v : Vertex) (hv : InStrip h v) :
    boxIndex v 1 ≤ boxIndex v 2 ∧ boxIndex v 2 ≤ boxIndex v 1 + (h : ℤ) := by
  cases v <;> simp [InStrip,boxIndex] at * <;> omega

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.StripWindows ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem mem_vertexWindow (h M : ℕ) (v : Vertex) : v ∈ vertexWindow h M ↔
    -(M : ℤ) ≤ boxIndex v 1 ∧ boxIndex v 1 ≤ M ∧ InStrip h v := by
  cases v <;>
    simp [vertexWindow,Finset.mem_biUnion,Finset.mem_Icc,
      Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton,InStrip,boxIndex,
      Vertex.up.injEq,Vertex.down.injEq] <;> aesop

theorem vertexWindow_convex (h M : ℕ) : AdmissiblyConvex (vertexWindow h M) := by
  apply admissiblyConvex_of_box _
    (fun k => if k = 0 then 0 else -(M : ℤ))
    (fun k => if k = 0 then h else if k = 1 then M+1 else M+h+1)
  intro v
  rw [mem_vertexWindow]
  constructor
  · rintro ⟨hlo,hhi,hstrip⟩ k
    have hb := strip_index_bounds h v hstrip
    fin_cases k <;> simp only [Fin.zero_eta,ite_true,Fin.reduceEq,ite_false]
    · exact hstrip
    · change -(M : ℤ) ≤ boxIndex v 1 ∧ boxIndex v 1 < (M : ℤ)+1
      omega
    · change -(M : ℤ) ≤ boxIndex v 2 ∧ boxIndex v 2 < (M : ℤ)+h+1
      omega
  · intro hv
    have h0 := hv 0
    have h1 := hv 1
    simp only [Fin.reduceEq,ite_false,ite_true] at h0 h1
    exact ⟨h1.1,by omega,h0⟩

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.vertexWindow_convex := @_root_.OAI.PolynomialVacuumBridge.Corridor.vertexWindow_convex
