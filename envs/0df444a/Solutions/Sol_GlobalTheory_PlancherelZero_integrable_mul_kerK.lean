-- Prove2me | solution 1 for GlobalTheory.PlancherelZero.integrable_mul_kerK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:19.130712+00:00
-- url     : https://prove2.me/submissions/d8b35a79-032d-4959-85fb-f81ee35caaf1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtale
import Theorems.Thm_GlobalTheory_PlancherelZero_continuous_kerK

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
theorem _root_.solution (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f : A.K → ℂ} (hf : IsTest f) (y : A.K) :
    Integrable (fun x => f x * A.kerK ψ x y) μ :=
  (hf.1.continuous.mul (continuous_kerK A ψ hψ y)).integrable_of_hasCompactSupport hf.2.mul_right
end GlobalTheory.PlancherelZero
