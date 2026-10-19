-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.outside_boundary_germ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:05:25.738117+00:00
-- url     : https://prove2.me/submissions/8a0fe9b0-71b5-4b46-b141-20e0d91f263a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BoundaryCharge.lean:L20-L36
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.outside_boundary_germ. The node keeps its source
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

theorem mem_starFaces (D : Finset Vertex) (a : FaceIndex) :
    a ∈ starFaces D ↔ ∃ v ∈ faceVertices a, v ∈ D := by
  simp only [starFaces,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,
    mem_faceVertices]
  aesop

theorem incident_mem_starFaces {D : Finset Vertex} {v : Vertex} (hv : v ∈ D)
    (k : Fin 3) : leftFace (v,k) ∈ starFaces D := by
  apply (mem_starFaces D _).mpr
  exact ⟨v,(mem_faceVertices _ _).mpr ⟨k,rfl⟩,hv⟩

theorem box_opposite_face (lo hi : Fin 3 → ℤ) (v r : Vertex) (k : Fin 3)
    (hv : BoxMem lo hi (neighbor v k))
    (hr : r ∈ faceVertices (leftFace (v,k+1)))
    (hr' : BoxMem lo hi r) : BoxMem lo hi v := by
  cases v <;> fin_cases k <;>
    simp only [leftFace,Fin.reduceAdd,Fin.zero_eta,Fin.isValue,Fin.reduceEq,ite_true,
      ite_false,faceVertices,Finset.mem_insert,Finset.mem_singleton] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem outside_opposite_face (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (v : Vertex) (k : Fin 3) (hv : v ∉ D) (hn : neighbor v k ∈ D) :
    leftFace (v,k+1) ∉ starFaces D := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  intro hf
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp hf
  exact hv ((hbox v).mpr (box_opposite_face lo hi v r k ((hbox _).mp hn) hr
    ((hbox _).mp hr')))

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.BoundaryCharge ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem outside_boundary_germ (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (v : Vertex) (k : Fin 3) (hv : v ∉ D) (hn : neighbor v k ∈ D) :
    OnFaceBoundary (starFaces D) (v,k+1) ∧
      faceBoundaryTurn (starFaces D) (v,k+1) = false := by
  have hR : rightFace (v,k) ∈ starFaces D := incident_mem_starFaces hn k
  have hL : leftFace (v,k) ∈ starFaces D := by
    have h := incident_mem_starFaces hn (k+2)
    simpa only [← rightFace_prev,rightFace,reverseGerm,neighbor_neighbor] using h
  have hO := outside_opposite_face D hD v k hv hn
  constructor
  · refine ⟨hO,?_⟩
    rw [rightFace_prev]
    convert hL using 1
    congr 2
    fin_cases k <;> decide
  · rw [faceBoundaryTurn_false]
    simpa only [rightFace_prev,add_assoc,Fin.reduceAdd] using hR

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.outside_boundary_germ := @_root_.OAI.PolynomialVacuumBridge.Corridor.outside_boundary_germ
