-- Prove2me | solution 1 for GlobalTheory.JR.PiSelfDual.intLat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:09:43.47896+00:00
-- url     : https://prove2.me/submissions/93da3495-aedc-42dc-9281-fed96a179c00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PiSelfDual
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
namespace GlobalTheory.JR.PiSelfDual
theorem _root_.solution (r : ℕ) :
    ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) =
      Set.univ.pi (fun _ => Metric.closedBall (0 : E) 1) := by
  ext b
  simp [intLat, Metric.mem_closedBall, dist_zero_right]
end GlobalTheory.JR.PiSelfDual
