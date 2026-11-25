-- Prove2me | solution 1 for GroundTheory.LocalField.integerInclusion_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:06:55.8247+00:00
-- url     : https://prove2.me/submissions/85f08be8-54df-4ab0-9dbf-886be29edc88

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K Ω : Type*} [Field K] [Field Ω] [ValuativeRel Ω] [Algebra K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution [ValuativeRel K] [ValuativeExtension K Ω]
    {E F : IntermediateField K Ω} (h : E ≤ F) : Function.Injective (integerInclusion h) := by
  intro x y hxy
  have := congrArg (fun z : 𝒪[F] ↦ ((z : F) : Ω)) hxy
  exact Subtype.ext (Subtype.ext this)
end GroundTheory.LocalField
