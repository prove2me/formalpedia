-- Prove2me | solution 1 for GroundTheory.Global.adeleMeasure_fundamentalSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:41.428748+00:00
-- url     : https://prove2.me/submissions/db2ce4ac-8ebd-4e40-a7d2-3706ded98ab6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Theorems.Thm_GroundTheory_Global_finiteAdeleMeasure_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_adeleMeasure_prod
import Theorems.Thm_GroundTheory_Global_infiniteAdeleMeasure_fundamentalSetInfinite

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
open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution : adeleMeasure K (fundamentalSet K) = 1 := by
  rw [fundamentalSet, adeleMeasure_prod, infiniteAdeleMeasure_fundamentalSetInfinite,
    finiteAdeleMeasure_integralFiniteAdeles, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (sqrt_discr_ne_zero K), ENNReal.coe_one]
end GroundTheory.Global
