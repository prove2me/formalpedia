-- Prove2me | solution 1 for GlobalTheory.eventually_isUnit_and_tendsto_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:49.975652+00:00
-- url     : https://prove2.me/submissions/0d98b931-94d3-40ba-8918-bbeb9efb8ac1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EventuallyTestFunctionMulInverseUnitEq
import Theorems.Thm_GlobalTheory_eventually_isUnit_and_tendsto_inverse_normed
import Theorems.Thm_GlobalTheory_finiteNormedAlgebra_eq_moduleTopology


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
    [CompleteSpace F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  classical
  have hτ : τ = moduleTopology F R := eq_moduleTopology F R
  let b := Module.finBasis F R
  let : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  let : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  let N : NormedCommRing R := NormedCommRing.induced R _ (Algebra.leftMulMatrix b)
    (Algebra.leftMulMatrix_injective b)
  let A : @NormedAlgebra F R _ N.toNormedRing.toSeminormedRing :=
    NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := @eventually_isUnit_and_tendsto_inverse_normed F _ _ R N A ‹_›
  have hN : N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R :=
    @finiteNormedAlgebra_eq_moduleTopology F _ _ R N A ‹_›
  rw [hτ, ← hN]
  exact key
end GlobalTheory
