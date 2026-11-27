-- Prove2me | solution 1 for GroundTheory.LocalField.IsTameSubextension.of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:52:56.683082+00:00
-- url     : https://prove2.me/submissions/07c13cda-bc18-4a74-974a-58725991e00b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
import Definitions.Def_GroundTheory_LocalFields_RamificationTameStructure
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_TameExtension
import Theorems.Thm_GroundTheory_LocalField_finiteDimensional_of_le

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
open Polynomial IntermediateField ValuativeRel
open GroundTheory GroundTheory.LocalField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
namespace GroundTheory.LocalField
namespace IsTameSubextension
theorem _root_.solution {E F : IntermediateField K Ω} (hF : IsTameSubextension F)
    (h : E ≤ F) : IsTameSubextension E := by
  have := hF.1
  have : FiniteDimensional K E := finiteDimensional_of_le h
  set F' := extendScalars h
  have : FiniteDimensional K F' := (inferInstance : FiniteDimensional K F)
  have : FiniteDimensional E F' := Module.Finite.of_restrictScalars_finite K E F'
  rw [isTameSubextension_iff]
  have he : ramificationIndex K F = ramificationIndex K E * ramificationIndex E F' :=
    ramificationIndex_restrictScalars E F'
  exact Nat.Coprime.coprime_dvd_left (Dvd.intro _ he.symm) hF.coprime
end IsTameSubextension
end GroundTheory.LocalField
