-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.top_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:15.49747+00:00
-- url     : https://prove2.me/submissions/2360179d-afb0-4e57-98bb-22f293dcbddd

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
namespace GlobalTheory.JR.EtMeas
theorem _root_.solution (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] :
    IsTopologicalAddGroup V ∧ T2Space V ∧ LocallyCompactSpace V ∧ SecondCountableTopology V ∧
      ∃ S : Set V, IsOpen S ∧ IsCompact S ∧ S.Nonempty := by
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup F V
  let b := Module.finBasis F V
  have : T2Space V := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  let e := b.equivFunL.toHomeomorph
  refine ⟨‹_›, ‹_›, e.isOpenEmbedding.locallyCompactSpace, e.secondCountableTopology,
    e ⁻¹' Metric.closedBall 0 1, ?_, ?_, ?_⟩
  · exact (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage e.continuous
  · exact e.isCompact_preimage.2 (isCompact_closedBall _ _)
  · exact ⟨e.symm 0, by simp⟩
end GlobalTheory.JR.EtMeas
