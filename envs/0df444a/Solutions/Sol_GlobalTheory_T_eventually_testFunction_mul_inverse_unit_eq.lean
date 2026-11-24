-- Prove2me | solution 1 for GlobalTheory.T.eventually_testFunction_mul_inverse_unit_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:13.342823+00:00
-- url     : https://prove2.me/submissions/50479f07-10d6-4c71-ab42-81579adb22b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EventuallyTestFunctionMulInverseUnitEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EventuallyTestFunctionMulInverseUnitEqStatement
import Theorems.Thm_GlobalTheory_eventually_testFn_mul_inverse_eq


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ s in 𝓝 a, ∀ t : A.K, IsUnit t → φ' (s * Ring.inverse t, t) = φ' (a * Ring.inverse t, t) := by
  first | exact @GlobalTheory.eventually_testFn_mul_inverse_eq | exact GlobalTheory.eventually_testFn_mul_inverse_eq | (intros; apply GlobalTheory.eventually_testFn_mul_inverse_eq <;> assumption)
end _root_.GlobalTheory.T
