-- Prove2me | solution 1 for GroundTheory.Global.finite_setOf_not_isIntegralUnitAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:11.130616+00:00
-- url     : https://prove2.me/submissions/cde3fb96-b6f8-4e0d-a993-8e6e5d6e9a45

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (u : (𝔸ᶠ[K])ˣ) :
    {v | ¬ IsIntegralUnitAt u v}.Finite :=
  Filter.eventually_cofinite.1 ((u : 𝔸ᶠ[K]).2.and ((u⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]).2)
end GroundTheory.Global
