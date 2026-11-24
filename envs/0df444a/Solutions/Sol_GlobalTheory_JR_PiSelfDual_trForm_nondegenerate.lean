-- Prove2me | solution 1 for GlobalTheory.JR.PiSelfDual.trForm_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:40:12.818375+00:00
-- url     : https://prove2.me/submissions/76d9e4b0-c86d-4b60-abd8-24cf54971131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_trForm_isSymm
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_trForm_separatingLeft

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
theorem _root_.solution (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate :=
  ⟨fun c hc => trForm_separatingLeft r c hc, fun b hb => trForm_separatingLeft r b (fun c => by
    rw [(trForm_isSymm (F := F) r).eq]; exact hb c)⟩
end GlobalTheory.JR.PiSelfDual
