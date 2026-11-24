-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.exists_selfDual_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:28:18.667458+00:00
-- url     : https://prove2.me/submissions/fdfa3473-da8c-4f4a-a772-e253d2409f87

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
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_formL_apply
import Theorems.Thm_GlobalTheory_JR_AbsInv_exists_selfDual
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure


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
theorem _root_.solution [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.Kˣ) :
    ∃ μ : Measure A.L, SelfDual μ (A.kerL ψ x) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := finite_L A
  obtain ⟨-, hinj, -, htr, hnd⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hs : (formL A x).IsSymm := ⟨fun y y' => by
    rw [formL_apply, formL_apply]
    congr 2
    apply hinj
    rw [htr, htr]; simp [add_comm, mul_comm]⟩
  have hl : ∀ y', (∀ y, formL A x y' y = 0) → y' = 0 := fun y' h => hnd y' fun y => by
    have h1 : (x : A.K) * Algebra.trace A.K A.L (star y' * y) = 0 := eq_zero_of_trace F A.K _ fun k => by
      have := h (k • y)
      rw [formL_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    simpa using h1
  exact exists_selfDual F ψ hψ A.L (formL A x) hs ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩
end GlobalTheory.JR.EtMeas
