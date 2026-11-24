-- Prove2me | solution 1 for GlobalTheory.WhitCollapse.measurable_etaK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:04.476678+00:00
-- url     : https://prove2.me/submissions/53862eb1-e226-49f7-b1d7-fc7c20f2dcf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierEtaleKEqIntegralPartialFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerIntegralEqVolumeMulIntegralPer
import Theorems.Thm_GlobalTheory_WhitCollapse_continuous_normF
import Theorems.Thm_GlobalTheory_T_unramifiedValuationParitySign_character_kernel_norms


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
open GlobalTheory GlobalTheory.WhitCollapse
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.WhitCollapse
theorem _root_.solution [Unram F E] (A : Et F E) : Measurable A.etaK := by
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  obtain ⟨-, -, -, hlc⟩ := GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E
  have hc : ContinuousOn (eta : F → ℂ) {0}ᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    exact hlc.continuous
  have hm : Measurable (eta : F → ℂ) := measurable_of_continuousOn_compl_singleton 0 hc
  exact hm.comp (continuous_normF A).measurable
end GlobalTheory.WhitCollapse
