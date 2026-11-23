-- Prove2me | solution 1 for GlobalTheory.JR.SelfDualLat.topo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:57:58.442432+00:00
-- url     : https://prove2.me/submissions/8a7d0620-5a40-43d6-bf05-ee992d630f8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SelfDualLat
namespace GlobalTheory.JR.SelfDualLat
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V], LocallyCompactSpace V ∧ SecondCountableTopology V ∧ T2Space V ∧ IsTopologicalAddGroup V := by
  intro F E _ _ _ _ _ V _ _ _ _ _
  haveI := (inferInstance : Unram F E).lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : ContinuousNeg V := ⟨by
    have := IsModuleTopology.continuous_of_linearMap (R := F) (A := V) (B := V) (-LinearMap.id)
    exact this⟩
  let e : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : V ≃ₜ (Fin (Module.finrank F V) → F) := ⟨e.toEquiv, hc, hc'⟩
  exact ⟨h.isOpenEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space,
    IsTopologicalAddGroup.mk⟩
end GlobalTheory.JR.SelfDualLat
