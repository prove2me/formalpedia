-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.exists_selfDual_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:28:19.671816+00:00
-- url     : https://prove2.me/submissions/3c8b1392-ab0b-4431-8cc4-6f464b727d41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousDistribHaarCharUnitsOfCompactOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsHaarQuotientIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Theorems.Thm_GlobalTheory_JR_EtMeas_exists_selfDual
import Theorems.Thm_GlobalTheory_JR_EtMeas_eq_zero_of_trace
import Theorems.Thm_GlobalTheory_JR_AbsInv_exists_selfDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtMeas
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.EtMeas
theorem _root_.solution [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    ∃ μ : Measure A.K, SelfDual μ (A.kerK ψ) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have hs : (Algebra.traceForm F A.K).IsSymm := ⟨fun x y => by simp [mul_comm]⟩
  refine exists_selfDual F ψ hψ A.K (Algebra.traceForm F A.K) hs ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact eq_zero_of_trace F A.K x fun y => by simpa using hx y
  · exact eq_zero_of_trace F A.K x fun y => by simpa [mul_comm] using hx y
end GlobalTheory.JR.EtMeas
