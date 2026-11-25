-- Prove2me | solution 1 for GroundTheory.Global.finiteAdeleMeasure_integralFiniteAdeles_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:50:35.022824+00:00
-- url     : https://prove2.me/submissions/883fc9f2-c5ef-4c54-8855-9731d60ad128

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Theorems.Thm_GroundTheory_Global_finiteAdeleMeasure_integralFiniteAdeles


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
variable (K)
namespace GroundTheory.Global
theorem _root_.solution :
    finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) ≠ ∞ := by
  rw [finiteAdeleMeasure_integralFiniteAdeles]
  exact ENNReal.coe_ne_top
end GroundTheory.Global
