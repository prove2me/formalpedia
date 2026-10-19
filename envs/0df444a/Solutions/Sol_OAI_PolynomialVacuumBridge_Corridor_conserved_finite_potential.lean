-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.conserved_finite_potential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:33:41.039127+00:00
-- url     : https://prove2.me/submissions/ac556d39-9518-4e8b-860d-c095ff6533e6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/PotentialSupport.lean:L17-L41
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.conserved_finite_potential. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_QFlow_finite_flow_is_face_boundary

-- ---- from OAI.Combinatorics.HoneycombCorridor.PotentialSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem conserved_finite_potential (q : EdgeIndex →₀ ℚ) (hq : ConservedCurrent q) :
    ∃ r : FaceIndex →₀ ℚ, faceGradient r = q := by
  let q' : QFlow.FiniteHoneycombFlow := {
    q0 := rationalFlowComponent q 0
    q1 := rationalFlowComponent q 1
    q2 := rationalFlowComponent q 2
    up_conservation := by
      intro i j
      change q ((i,j),0) + q ((i,j),1) + q ((i,j),2) = 0
      simpa [directedCurrent,dartSign,edgeOf,Fin.sum_univ_succ,add_assoc] using hq (.up i j)
    down_conservation := by
      intro i j
      have h := hq (.down i j)
      simp [directedCurrent,dartSign,edgeOf,Fin.sum_univ_succ] at h
      change q ((i,j+1),0) + q ((i,j),1) + q ((i+1,j),2) = 0
      linarith }
  obtain ⟨r,hr⟩ := QFlow.finite_flow_is_face_boundary q'
  refine ⟨r,?_⟩
  funext e
  rcases e with ⟨⟨i,j⟩,k⟩
  have h := hr i j
  change q ((i,j),0) = _ ∧ q ((i,j),1) = _ ∧ q ((i,j),2) = _ at h
  fin_cases k <;>
    simp [faceGradient,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] <;>
    tauto

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.conserved_finite_potential := @_root_.OAI.PolynomialVacuumBridge.Corridor.conserved_finite_potential
