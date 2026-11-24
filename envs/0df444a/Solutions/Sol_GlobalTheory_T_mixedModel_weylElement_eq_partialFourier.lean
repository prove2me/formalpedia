-- Prove2me | solution 1 for GlobalTheory.T.mixedModel_weylElement_eq_partialFourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:13:24.998486+00:00
-- url     : https://prove2.me/submissions/cab88041-ed75-4ae2-a68b-3bf99e4e6641

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelWeylElementEqPartialFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelWeylElementEqPartialFourierStatement
import Theorems.Thm_GlobalTheory_JR_WeilMix_negB_ptrB_wS_ptrB


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → WeilMix.negB (WeilMix.ptrB M ψ (WeilMix.rowAct (wS F) (WeilMix.ptrB M ψ f))) = fourG M ψ f := by
  first | exact @GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | exact GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB | (intros; apply GlobalTheory.JR.WeilMix.negB_ptrB_wS_ptrB <;> assumption)
end _root_.GlobalTheory.T
