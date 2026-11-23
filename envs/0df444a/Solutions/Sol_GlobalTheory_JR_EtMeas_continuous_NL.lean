-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.continuous_NL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:19.752961+00:00
-- url     : https://prove2.me/submissions/5b7aee5d-0958-4e2d-976c-42b6a3faa3ab

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
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
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
theorem _root_.solution [U : Unram F E] (A : Et F E) : Continuous A.NL := by
  have := finite_L A
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (IsScalarTower.toAlgHom F A.K A.L).toLinearMap
    (LinearMap.ker_eq_bot.2 hinj)
  have h1 : A.NL = fun y => r (y * starF A y) := by
    funext y
    have := LinearMap.congr_fun hr (A.NL y)
    rw [← show _ = A.NL y from this]
    exact congrArg r (hN y)
  rw [h1]
  exact (IsModuleTopology.continuous_of_linearMap r).comp
    (continuous_id.mul (IsModuleTopology.continuous_of_linearMap (starF A)))
end GlobalTheory.JR.EtMeas
