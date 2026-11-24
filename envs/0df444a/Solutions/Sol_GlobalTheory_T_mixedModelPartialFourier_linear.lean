-- Prove2me | solution 1 for GlobalTheory.T.mixedModelPartialFourier_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:23.701281+00:00
-- url     : https://prove2.me/submissions/0a2ba234-18a4-4ec4-aacb-91011cf7a0cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierLinearStatement
import Theorems.Thm_GlobalTheory_JR_WeilMix_ptrB_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_linear | exact GlobalTheory.JR.WeilMix.ptrB_linear | (intros; apply GlobalTheory.JR.WeilMix.ptrB_linear <;> assumption)
end _root_.GlobalTheory.T
