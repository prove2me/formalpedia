-- Prove2me | solution 1 for GroundTheory.Global.infiniteAdeleMeasure_fundamentalSetInfinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:43:42.299799+00:00
-- url     : https://prove2.me/submissions/4a5b1882-45b6-44b5-9a1a-c4094090919e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Theorems.Thm_GroundTheory_Global_measurePreserving_measurableEquivMixedSpace

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
theorem _root_.solution :
    infiniteAdeleMeasure K (fundamentalSetInfinite K) = (NNReal.sqrt ‖discr K‖₊ : ℝ≥0∞) := by
  change infiniteAdeleMeasure K ((measurableEquivMixedSpace K) ⁻¹'
    ZSpan.fundamentalDomain (latticeBasis K)) = _
  rw [(measurePreserving_measurableEquivMixedSpace K).measure_preimage_equiv, selfDualMeasure,
    Measure.smul_apply, volume_fundamentalDomain_latticeBasis, smul_eq_mul, ← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
end GroundTheory.Global
