-- Prove2me | solution 1 for GroundTheory.Global.norm_uniformizerUnit_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:10.876237+00:00
-- url     : https://prove2.me/submissions/817ccb59-e1cb-4ca2-84af-d16c31613c35

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
import Theorems.Thm_GroundTheory_Global_normalizedAbv_apply
import Theorems.Thm_GroundTheory_Global_normalizedAbv_of_irreducible


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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    ‖((uniformizerUnit v ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-n) := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, uniformizerUnit, Units.val_mk0, ← normalizedAbv_apply,
    normalizedAbv_of_irreducible v (irreducible_uniformizerAt v), inv_zpow', zpow_neg]
end GroundTheory.Global
