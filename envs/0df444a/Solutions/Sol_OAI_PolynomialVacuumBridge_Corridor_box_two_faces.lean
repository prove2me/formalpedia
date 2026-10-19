-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.box_two_faces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:59:36.285978+00:00
-- url     : https://prove2.me/submissions/3e7f731d-b5b1-4034-adb1-67fe0a1cb367

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Convexity.lean:L191-L206
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.box_two_faces. The node keeps its source
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

theorem box_two_faces_up0 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.up i j,0)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.up i j) ((0 : Fin 3)+1),(0 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.up i j) ∨ BoxMem lo hi (neighbor (.up i j) ((0 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_up1 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.up i j,1)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.up i j) ((1 : Fin 3)+1),(1 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.up i j) ∨ BoxMem lo hi (neighbor (.up i j) ((1 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_up2 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.up i j,2)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.up i j) ((2 : Fin 3)+1),(2 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.up i j) ∨ BoxMem lo hi (neighbor (.up i j) ((2 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_down0 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.down i j,0)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.down i j) ((0 : Fin 3)+1),(0 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.down i j) ∨ BoxMem lo hi (neighbor (.down i j) ((0 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_down1 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.down i j,1)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.down i j) ((1 : Fin 3)+1),(1 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.down i j) ∨ BoxMem lo hi (neighbor (.down i j) ((1 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces_down2 (lo hi : Fin 3 → ℤ) (i j : ℤ) (r s : Vertex)
    (hr : r ∈ faceVertices (rightFace (.down i j,2)))
    (hs : s ∈ faceVertices (leftFace
      (neighbor (.down i j) ((2 : Fin 3)+1),(2 : Fin 3)+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi (.down i j) ∨ BoxMem lo hi (neighbor (.down i j) ((2 : Fin 3)+1)) := by
  simp only [rightFace,reverseGerm,neighbor,leftFace,Fin.reduceAdd,
    Fin.isValue,Fin.reduceEq,ite_true,ite_false,faceVertices,Finset.mem_insert,
    Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [BoxMem,Fin.forall_fin_succ,boxIndex,neighbor] <;> omega

theorem box_two_faces (lo hi : Fin 3 → ℤ) (v r s : Vertex) (k : Fin 3)
    (hr : r ∈ faceVertices (rightFace (v,k)))
    (hs : s ∈ faceVertices (leftFace (neighbor v (k+1),k+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi v ∨ BoxMem lo hi (neighbor v (k+1)) := by
  cases v with
  | up i j =>
    fin_cases k
    · exact box_two_faces_up0 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_up1 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_up2 lo hi i j r s hr hs hr' hs'
  | down i j =>
    fin_cases k
    · exact box_two_faces_down0 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_down1 lo hi i j r s hr hs hr' hs'
    · exact box_two_faces_down2 lo hi i j r s hr hs hr' hs'

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.box_two_faces := @_root_.OAI.PolynomialVacuumBridge.Corridor.box_two_faces
