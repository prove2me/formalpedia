-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.admissiblyConvex_filled
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:21:22.153392+00:00
-- url     : https://prove2.me/submissions/00c10c2b-9be7-4a2e-bee0-0c1dbdcda184

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/ConvexDomains.lean:L72-L87
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.admissiblyConvex_filled. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_integer_bounds_fraction
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_tilingCoordinate_index

-- ---- from OAI.Combinatorics.HoneycombCorridor.PotentialSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem incident_faces_equal (p : FaceIndex →₀ ℤ) (v : Vertex)
    (hp : ∀ k : Fin 3, p (leftFace (v,k)) = p (rightFace (v,k)))
    (k l : Fin 3) : p (leftFace (v,k)) = p (leftFace (v,l)) := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  cases v <;> fin_cases k <;> fin_cases l <;>
    simp [leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Polygons ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

namespace Polygon
theorem potential_spec (P : Polygon) :
    RepresentsFlow P.potential (wordFlow P.germ P.turns) ∧ P.potential ≠ 0 ∧
    (P.orientation = 1 ∨ P.orientation = -1) ∧
    ∀ a, P.potential a = 0 ∨ P.potential a = P.orientation :=
  P.has_indicator.choose_spec.choose_spec

end Polygon

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.PolygonGeometry ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

namespace Polygon

end Polygon

namespace Polygon

theorem represents (P : Polygon) : RepresentsFlow P.potential (wordFlow P.germ P.turns) :=
  P.potential_spec.1

theorem off_boundary_zero (P : Polygon) (v : Vertex) (hv : v ∉ P.vertices) (k : Fin 3) :
    orientedFlow (wordFlow P.germ P.turns) (v,k) = 0 := by
  apply (orientedFlow_zero_iff _ _).mpr
  by_contra hn
  apply hv
  change v ∈ edgeVertices P.val
  apply (mem_edgeVertices _ _).mpr
  exact ⟨k,by rw [← P.traversal.2.2.2]; exact Finsupp.mem_support_iff.mpr hn⟩

theorem off_boundary_faces (P : Polygon) (v : Vertex) (hv : v ∉ P.vertices) (k : Fin 3) :
    P.potential (leftFace (v,k)) = vertexLevel P.potential v ∧
    P.potential (rightFace (v,k)) = vertexLevel P.potential v := by
  have he (l : Fin 3) : P.potential (leftFace (v,l)) = P.potential (rightFace (v,l)) := by
    have h := P.represents (v,l)
    rw [P.off_boundary_zero v hv l] at h
    omega
  have hl := incident_faces_equal P.potential v he k 0
  exact ⟨hl,(he k).symm.trans hl⟩

theorem interior_iff_level (P : Polygon) (v : Vertex) :
    v ∈ P.interior ↔ v ∉ P.vertices ∧ vertexLevel P.potential v ≠ 0 := by
  rw [P.mem_interior,mem_cellVertices]
  constructor
  · rintro ⟨⟨k,hk⟩,hv⟩
    refine ⟨hv,?_⟩
    change leftFace (v,k) ∈ P.potential.support at hk
    rw [Finsupp.mem_support_iff] at hk
    rwa [(P.off_boundary_faces v hv k).1] at hk
  · rintro ⟨hv,hl⟩
    exact ⟨⟨0,Finsupp.mem_support_iff.mpr hl⟩,hv⟩

theorem step_level (P : Polygon) (v : Vertex) (k : Fin 3)
    (hv : v ∉ P.vertices) (hu : neighbor v k ∉ P.vertices) :
    vertexLevel P.potential (neighbor v k) = vertexLevel P.potential v := by
  rw [← (P.off_boundary_faces (neighbor v k) hu k).1]
  change P.potential (leftFace (reverseGerm (v,k))) = _
  exact (P.off_boundary_faces v hv k).2

theorem interior_exit_on_boundary (P : Polygon) (v : Vertex) (k : Fin 3)
    (hv : v ∈ P.interior) (hu : neighbor v k ∉ P.interior) :
    neighbor v k ∈ P.vertices := by
  by_contra hn
  apply hu
  rw [P.interior_iff_level]
  have h := (P.interior_iff_level v).mp hv
  exact ⟨hn,by rw [P.step_level v k h.1 hn]; exact h.2⟩

end Polygon
end PolynomialVacuumBridge.Corridor

end

end OAI

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

-- ---- from OAI.Combinatorics.HoneycombCorridor.ConvexDomains ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem coordinateIndex_box_iff (lo hi : Fin 3 → ℤ) (v : Vertex) (k : Fin 3) :
    (3*lo k < coordinateIndex v k ∧ coordinateIndex v k < 3*hi k) ↔
      lo k ≤ boxIndex v k ∧ boxIndex v k < hi k := by
  cases v <;> fin_cases k <;> simp [coordinateIndex,boxIndex] <;> omega

theorem coordinateIndex_increase (v : Vertex) (k : Fin 3) :
    ∃ l : Fin 3, coordinateIndex v k < coordinateIndex (neighbor v l) k := by
  cases v <;> fin_cases k
  all_goals first
    | (refine ⟨0,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨1,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨2,?_⟩; simp [coordinateIndex,neighbor]; omega)

theorem coordinateIndex_decrease (v : Vertex) (k : Fin 3) :
    ∃ l : Fin 3, coordinateIndex (neighbor v l) k < coordinateIndex v k := by
  cases v <;> fin_cases k
  all_goals first
    | (refine ⟨0,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨1,?_⟩; simp [coordinateIndex,neighbor] <;> omega)
    | (refine ⟨2,?_⟩; simp [coordinateIndex,neighbor]; omega)

theorem Polygon.interior_maximum_principle (P : Polygon) (f : Vertex → ℤ)
    (hf : ∀ v, ∃ k : Fin 3, f v < f (neighbor v k)) (M : ℤ)
    (hbd : ∀ v ∈ P.vertices, f v < M) : ∀ v ∈ P.interior, f v < M := by
  classical
  intro v hv
  let R := P.interior.image f
  have hvR : f v ∈ R := Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have hne : R.Nonempty := ⟨f v,hvR⟩
  let m := R.max' hne
  obtain ⟨u,hu,hum⟩ := Finset.mem_image.mp (R.max'_mem hne)
  obtain ⟨k,hk⟩ := hf u
  have hn : neighbor u k ∉ P.interior := by
    intro hn
    have hle := R.le_max' _ (Finset.mem_image.mpr ⟨neighbor u k,hn,rfl⟩)
    change f (neighbor u k) ≤ m at hle
    change f u = m at hum
    omega
  have hb := P.interior_exit_on_boundary u k hu hn
  have hbound := hbd _ hb
  have hle := R.le_max' (f v) hvR
  change f v ≤ m at hle
  change f u = m at hum
  omega

theorem admissiblyConvex_filled (D : Finset Vertex) (hD : AdmissiblyConvex D) : Filled D := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  intro P hP v hv
  apply (hbox v).mpr
  intro k
  apply (coordinateIndex_box_iff lo hi v k).mp
  have hp : P.vertices ⊆ D := (mem_polygons D P).mp hP
  have hbd (u : Vertex) (hu : u ∈ P.vertices) :
      3*lo k < coordinateIndex u k ∧ coordinateIndex u k < 3*hi k :=
    (coordinateIndex_box_iff lo hi u k).mpr ((hbox u).mp (hp hu) k)
  have hh := P.interior_maximum_principle (fun u => coordinateIndex u k)
    (fun u => coordinateIndex_increase u k) (3*hi k) (fun u hu => (hbd u hu).2) v hv
  have hl := P.interior_maximum_principle (fun u => -coordinateIndex u k)
    (fun u => by obtain ⟨l,hl⟩ := coordinateIndex_decrease u k; exact ⟨l,by omega⟩)
    (-3*lo k) (fun u hu => by have := (hbd u hu).1; omega) v hv
  omega

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.admissiblyConvex_filled := @_root_.OAI.PolynomialVacuumBridge.Corridor.admissiblyConvex_filled
