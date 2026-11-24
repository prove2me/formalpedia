-- Prove2me | solution 1 for GlobalTheory.JR.MeasScale.kerL_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:01:23.176264+00:00
-- url     : https://prove2.me/submissions/a7f8fa8d-1253-41f7-846c-94137d8752f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale
import Theorems.Thm_GlobalTheory_JR_MeasScale_unitL_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MeasScale
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.MeasScale
theorem _root_.solution (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (y' y : A.L) :
    A.kerL ψ ((1 : A.Kˣ) : A.K) y' (unitL A x • y) = A.kerL ψ ((1 : A.Kˣ) : A.K) (unitL A x • y') y := by
  simp only [Et.kerL, unitL_smul]
  rw [star_mul', A.star_K]
  congr 3
  ring
end GlobalTheory.JR.MeasScale
