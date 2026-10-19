-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.nonboundary_cellCurvature
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:44:20.737885+00:00
-- url     : https://prove2.me/submissions/2e10b97f-3fcb-47a7-833d-38363f398eeb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Curvature.lean:L197-L214
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.nonboundary_cellCurvature. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_nonboundary_vertex_all_edges

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

-- ---- from OAI.Combinatorics.HoneycombCorridor.Curvature ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem nonboundary_cellCurvature (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) (p : FaceIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) (v : Vertex)
    (hv : v ∈ cellVertices p.support) (hnot : v ∉ traced g w) :
    cellCurvature p.support v = 0 := by
  have hE := nonboundary_vertex_all_edges g w hc p hp v hv hnot
  have hz (l : Fin 3) : orientedFlow (wordFlow g w) (v,l) = 0 := by
    rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
    exact turnVisit_eq_zero_of_not_mem g w v l hnot
  have he (l : Fin 3) : p (leftFace (v,l)) = p (rightFace (v,l)) := by
    have h := hp (v,l)
    rw [hz l] at h
    omega
  obtain ⟨l,hl⟩ := (mem_cellVertices _ v).mp hv
  have hF (k : Fin 3) : leftFace (v,k) ∈ p.support := by
    rw [Finsupp.mem_support_iff] at hl ⊢
    rwa [incident_faces_equal p v he k l]
  simp [cellCurvature,edgeCount,faceCount,hE,hF]

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.nonboundary_cellCurvature := @_root_.OAI.PolynomialVacuumBridge.Corridor.nonboundary_cellCurvature
