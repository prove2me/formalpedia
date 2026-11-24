-- Prove2me | solution 1 for GlobalTheory.JR.PiSelfDual.isModuleTopology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:42.924828+00:00
-- url     : https://prove2.me/submissions/78e27130-ff75-4a16-a826-cd968ecde2b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_finite

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
theorem _root_.solution : IsModuleTopology F E := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : Module.Finite F E := finite
  exact IsModuleTopology.iso (R := F) (A := Fin 2 → F)
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Unram.finrank_eq (F := F) (E := E)]))
end GlobalTheory.JR.PiSelfDual
