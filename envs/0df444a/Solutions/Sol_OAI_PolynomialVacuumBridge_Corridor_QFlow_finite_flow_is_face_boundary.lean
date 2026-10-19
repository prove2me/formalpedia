-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.QFlow.finite_flow_is_face_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:30:51.619119+00:00
-- url     : https://prove2.me/submissions/2ba6fabe-4459-44ed-8db1-b265d58b0aca

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/RationalPotential.lean:L170-L185
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.QFlow.finite_flow_is_face_boundary. The node keeps its source
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

-- ---- from OAI.Combinatorics.HoneycombCorridor.RationalPotential ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor.QFlow

theorem finite_flow_is_face_boundary (q : FiniteHoneycombFlow) :
    ∃ p : FaceIndex →₀ ℚ, ∀ i j,
      q.q0 (i,j) = p (i,j) - p (i-1,j) ∧
      q.q1 (i,j) = p (i-1,j+1) - p (i,j) ∧
      q.q2 (i,j) = p (i-1,j) - p (i-1,j+1) := by
  refine ⟨finiteFlowPotential q, ?_⟩
  intro i j
  have h0 := facePrefix_difference q.q0 i j
  have h2 := flowPotential_vertical q (i-1) j
  have hu := q.up_conservation i j
  simp only [sub_add_cancel] at h2
  simp only [finiteFlowPotential,Finsupp.ofSupportFinite_coe,flowPotential]
  dsimp [flowPotential] at h2
  constructor
  · linarith
  constructor <;> linarith

end PolynomialVacuumBridge.Corridor.QFlow

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor OAI.PolynomialVacuumBridge.Corridor.QFlow


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.QFlow.finite_flow_is_face_boundary := @_root_.OAI.PolynomialVacuumBridge.Corridor.QFlow.finite_flow_is_face_boundary
