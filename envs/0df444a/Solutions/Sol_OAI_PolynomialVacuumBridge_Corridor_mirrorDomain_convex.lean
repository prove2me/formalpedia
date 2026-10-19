-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.mirrorDomain_convex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:36:27.620339+00:00
-- url     : https://prove2.me/submissions/c17cf0d5-b811-4bd6-b47a-c9b957dc514b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Reflection.lean:L95-L124
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.mirrorDomain_convex. The node keeps its source
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

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Reflection ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem mirrorDomain_convex (D : Finset Vertex) (hD : AdmissiblyConvex D) :
    AdmissiblyConvex (mirrorDomain D) := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  let lo' : Fin 3 → ℤ := fun k => if k = 0 then lo 0 else if k = 1 then 1-hi 2 else 1-hi 1
  let hi' : Fin 3 → ℤ := fun k => if k = 0 then hi 0 else if k = 1 then 1-lo 2 else 1-lo 1
  apply admissiblyConvex_of_box _ lo' hi'
  intro v
  rw [mem_mirrorDomain,hbox]
  have hm := mirror_indices v
  constructor
  · intro hv k
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    rw [hm.1] at h0
    rw [hm.2.1] at h1
    rw [hm.2.2] at h2
    fin_cases k <;> simp [lo',hi'] <;> omega
  · intro hv k
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    simp only [lo',hi',Fin.isValue,Fin.reduceEq,ite_true,ite_false] at h0 h1 h2
    fin_cases k
    · change lo 0 ≤ boxIndex (mirrorVertex v) 0 ∧ boxIndex (mirrorVertex v) 0 < hi 0
      rw [hm.1]; omega
    · change lo 1 ≤ boxIndex (mirrorVertex v) 1 ∧ boxIndex (mirrorVertex v) 1 < hi 1
      rw [hm.2.1]; omega
    · change lo 2 ≤ boxIndex (mirrorVertex v) 2 ∧ boxIndex (mirrorVertex v) 2 < hi 2
      rw [hm.2.2]; omega

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.mirrorDomain_convex := @_root_.OAI.PolynomialVacuumBridge.Corridor.mirrorDomain_convex
