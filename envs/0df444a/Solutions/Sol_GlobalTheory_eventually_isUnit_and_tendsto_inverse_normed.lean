-- Prove2me | solution 1 for GlobalTheory.eventually_isUnit_and_tendsto_inverse_normed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:02.629928+00:00
-- url     : https://prove2.me/submissions/8ee434a7-4e65-4703-9a3c-2f2fdb89e16c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EventuallyTestFunctionMulInverseUnitEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [NormedCommRing R] [NormedAlgebra F R] [Module.Finite F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  have : CompleteSpace R := FiniteDimensional.complete F R
  refine ⟨Units.isOpen.mem_nhds isUnit_one, ?_⟩
  have h := (NormedRing.inverse_continuousAt (1 : Rˣ)).tendsto
  simpa using h
end GlobalTheory
