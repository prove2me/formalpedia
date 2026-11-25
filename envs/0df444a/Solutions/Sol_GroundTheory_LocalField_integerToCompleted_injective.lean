-- Prove2me | solution 1 for GroundTheory.LocalField.integerToCompleted_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:21.654236+00:00
-- url     : https://prove2.me/submissions/67ed6ce7-8ed0-4c56-b0c5-ab65de0f4c56

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
import Theorems.Thm_GroundTheory_LocalField_integerInclusion_injective


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
theorem _root_.solution {L : IntermediateField K Ω} (h : L ≤ 𝔼) :
    Function.Injective (integerToCompleted K Ω h) :=
  (algebraMap_integer_completedUnramifiedIntegers_injective K Ω).comp (integerInclusion_injective h)
end GroundTheory.LocalField
