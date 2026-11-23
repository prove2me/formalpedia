-- Prove2me | solution 1 for GroundTheory.LocalField.residueAlgEquiv_residue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:13.514821+00:00
-- url     : https://prove2.me/submissions/bd27d548-46b3-44a1-ac98-8528bbf38021

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Topology Filter
variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    residueAlgEquiv K L σ (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] (integerAlgEquiv K L σ x) :=
  rfl
end GroundTheory.LocalField
