-- Prove2me | solution 1 for GlobalTheory.T.volume_scaledIntegers_mul_volume_dual_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:33.663312+00:00
-- url     : https://prove2.me/submissions/d0825ae4-79ff-47b1-a3ac-4862cb09cd59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_VolumeScaledIntegersMulVolumeDualEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_VolumeScaledIntegersMulVolumeDualEqOneStatement
import Theorems.Thm_GlobalTheory_EtaChar_main
import Theorems.Thm_GlobalTheory_JR_EtFacts_main
import Theorems.Thm_GlobalTheory_LatVol_main


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ c : F, c ≠ 0 → MeasurableSet {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ∧ (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * (((μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal : ℝ) : ℂ) = 1 := by
  first | exact @GlobalTheory.LatVol.main | exact GlobalTheory.LatVol.main | (intros; apply GlobalTheory.LatVol.main <;> assumption)
end _root_.GlobalTheory.T
