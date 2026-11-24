-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.borel_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:31.384449+00:00
-- url     : https://prove2.me/submissions/b93cfdb9-27b6-49de-9b70-fa1e3626af8e

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
theorem _root_.solution (R : Type) [CommRing R] [TopologicalSpace R] [IsOpenUnits R] [MeasurableSpace R] [BorelSpace R] :
    BorelSpace Rˣ := by
  have h := (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isInducing
  refine ⟨?_⟩
  have h1 := @borel_comap Rˣ R Units.val inferInstance
  rw [← BorelSpace.measurable_eq (α := R), ← h.eq_induced] at h1
  exact h1.symm
end GlobalTheory.JR.EtMeas
