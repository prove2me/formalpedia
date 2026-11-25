-- Prove2me | solution 1 for GroundTheory.Global.inv_uniformizerUnit_zpow_mul_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:10.576928+00:00
-- url     : https://prove2.me/submissions/f0a35d5d-20a2-4b32-8b33-6cc261dde6eb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
import Theorems.Thm_GroundTheory_Global_valued_uniformizerUnit_zpow
import Theorems.Thm_GroundTheory_Global_inv_mul_le_one_iff_withZero

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (n : ℤ)
    (y : v.adicCompletion K) :
    ((uniformizerUnit v ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ * y ∈
        v.adicCompletionIntegers K ↔ Valued.v y ≤ exp (-n) := by
  rw [mem_adicCompletionIntegers, map_mul, map_inv₀, valued_uniformizerUnit_zpow]
  exact inv_mul_le_one_iff_withZero exp_ne_zero
end GroundTheory.Global
