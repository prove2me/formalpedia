-- Prove2me | solution 1 for GlobalTheory.JR.PiSelfDual.trForm_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:11.534801+00:00
-- url     : https://prove2.me/submissions/a0d6f568-771d-4c23-be1d-465e5eb6745b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_trace_star
import Theorems.Thm_GlobalTheory_JR_PiSelfDual_trForm_apply

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
theorem _root_.solution (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [trForm_apply, trForm_apply, star_dotProduct, trace_star]
end GlobalTheory.JR.PiSelfDual
