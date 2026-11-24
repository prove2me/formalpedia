-- Prove2me | solution 1 for GlobalTheory.JR.MeasTransport.trForm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:21:11.338253+00:00
-- url     : https://prove2.me/submissions/1e03dbef-ee25-4d12-bad3-3a6f0b4e798f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapIsIsomSelfDualMeasureKerLEqPiHaar
import Theorems.Thm_GlobalTheory_JR_MeasTransport_trForm_apply
import Theorems.Thm_GlobalTheory_JR_MeasTransport_trace_star

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MeasTransport
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.MeasTransport
theorem _root_.solution [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun c b => ?_⟩
  rw [trForm_apply, trForm_apply, ← trace_star (F := F) (star b ⬝ᵥ c), ← star_dotProduct_star, star_star]
end GlobalTheory.JR.MeasTransport
