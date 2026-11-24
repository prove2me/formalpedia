-- Prove2me | solution 1 for GlobalTheory.JR.PartialInv.ptrB_ptrB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:38.610399+00:00
-- url     : https://prove2.me/submissions/1b0d61e1-91c2-41e3-ba9e-10d68c0f9a29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumn
import Theorems.Thm_GlobalTheory_JR_PartialInv_isTest_slice
import Theorems.Thm_GlobalTheory_JR_PartialInv_selfDual_pi

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PartialInv
namespace GlobalTheory.JR.PartialInv
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (f : Gl r F → ℂ) (hf : IsTest f) : WeilMix.ptrB M ψ (WeilMix.ptrB M ψ f) = WeilMix.negB f := by
  funext Y
  exact (selfDual_pi F E r M ψ hψ).2 _ (isTest_slice hf Y.1 Y.2.2.1 Y.2.2.2) Y.2.1
end GlobalTheory.JR.PartialInv
