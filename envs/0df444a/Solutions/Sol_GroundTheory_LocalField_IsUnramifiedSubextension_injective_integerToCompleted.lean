-- Prove2me | solution 1 for GroundTheory.LocalField.IsUnramifiedSubextension.injective_integerToCompleted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:34.407988+00:00
-- url     : https://prove2.me/submissions/df3c4aad-46af-41a4-a7be-0114a3607359

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
import Theorems.Thm_GroundTheory_LocalField_integerToCompleted_injective

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
open IsLocalRing ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
local notation "𝔹" => CompletedUnramifiedIntegers K Ω
variable {K Ω}
namespace GroundTheory.LocalField
namespace IsUnramifiedSubextension
theorem _root_.solution {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) :
    Function.Injective (integerToCompleted K Ω hL.le_maximalUnramifiedExtension) :=
  integerToCompleted_injective _
end IsUnramifiedSubextension
end GroundTheory.LocalField
