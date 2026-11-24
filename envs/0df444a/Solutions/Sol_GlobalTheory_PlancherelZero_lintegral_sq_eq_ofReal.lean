-- Prove2me | solution 1 for GlobalTheory.PlancherelZero.lintegral_sq_eq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:27:12.834482+00:00
-- url     : https://prove2.me/submissions/eda3c77f-de78-4270-8c5f-d0f86b50ff94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtale

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
open GlobalTheory GlobalTheory.PlancherelZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.PlancherelZero
theorem _root_.solution {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {g : X → ℂ} (hg : IsTest g) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hc : Continuous fun x => ‖g x‖ ^ 2 := (hg.1.continuous.norm).pow 2
  have hs : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ g) := hg.2.comp_left (by simp)
  rw [ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hs)
    (ae_of_all _ fun x => by simp only [Pi.zero_apply]; positivity)]
  congr 1; funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
end GlobalTheory.PlancherelZero
