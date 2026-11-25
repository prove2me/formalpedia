-- Prove2me | solution 1 for GroundTheory.Global.finiteAdeleMeasure_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:41:35.194659+00:00
-- url     : https://prove2.me/submissions/b9ff7d81-4369-43e4-b6d6-1e42fbaa25cd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Theorems.Thm_GroundTheory_Global_coe_integralFiniteAdelesPositiveCompacts

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
    finiteAdeleMeasure K (integralFiniteAdeles (𝓞 K) K) = ((NNReal.sqrt ‖discr K‖₊)⁻¹ : ℝ≥0) := by
  rw [finiteAdeleMeasure, Measure.smul_apply, ← coe_integralFiniteAdelesPositiveCompacts,
    addHaarMeasure_self, ENNReal.smul_def, smul_eq_mul, mul_one]
end GroundTheory.Global
