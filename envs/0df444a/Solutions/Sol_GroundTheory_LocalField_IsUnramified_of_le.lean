-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramified.of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:16:41.115792+00:00
-- url     : https://prove2.me/submissions/9a601897-9c51-4470-87fd-48df832cf57c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_of_tower_left
import Theorems.Thm_GroundTheory_LocalField_valuativeExtension_algHom


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
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
open GroundTheory GroundTheory.LocalField
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
namespace IsUnramified
theorem _root_.solution {E F : IntermediateField K L} (h : E ≤ F) [IsUnramified K F] :
    IsUnramified K E := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension E F := valuativeExtension_algHom (K := K) (IntermediateField.inclusion h)
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite K E F
  exact IsUnramified.of_tower_left K E F
end IsUnramified
end GroundTheory.LocalField
