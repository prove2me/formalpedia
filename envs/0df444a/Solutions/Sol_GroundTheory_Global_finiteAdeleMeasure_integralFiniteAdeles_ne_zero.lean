-- Prove2me | solution 1 for GroundTheory.Global.finiteAdeleMeasure_integralFiniteAdeles_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:49:49.786771+00:00
-- url     : https://prove2.me/submissions/c469a5ba-acee-49e5-92c1-8b767289d767

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
    finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) ≠ 0 := by
  rw [finiteAdeleMeasure_integralFiniteAdeles]
  exact ENNReal.coe_ne_zero.2 (inv_ne_zero (sqrt_discr_ne_zero K))
end GroundTheory.Global
