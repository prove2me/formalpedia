-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.Polygon.trace_left_potential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:52:48.012054+00:00
-- url     : https://prove2.me/submissions/42985cde-1efa-4153-9b65-93e02b574f2c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/PolygonGeometry.lean:L246-L260
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.Polygon.trace_left_potential. The node keeps its source
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

theorem trace_left_potential (P : Polygon) (g : Germ) (w : List Bool)
    (hdis : ∀ v ∈ traced g w, v ∉ P.vertices) :
    P.potential (leftFace (terminalGerm g w)) = P.potential (leftFace g) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
      have hg : g.1 ∉ P.vertices := hdis _ (by simp [traced])
      have htail : ∀ v ∈ traced (advance g b) w, v ∉ P.vertices := by
        intro v hv
        exact hdis v (List.mem_cons_of_mem _ hv)
      change P.potential (leftFace (terminalGerm (advance g b) w)) = _
      rw [ih (advance g b) htail]
      change P.potential (rightFace (g.1,outgoingSlot g b)) = _
      rw [(P.off_boundary_faces g.1 hg (outgoingSlot g b)).2]
      exact (P.off_boundary_faces g.1 hg g.2).1.symm

end Polygon
end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor OAI.PolynomialVacuumBridge.Corridor.Polygon


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.Polygon.trace_left_potential := @_root_.OAI.PolynomialVacuumBridge.Corridor.Polygon.trace_left_potential
