-- Prove2me | solution 1 for GroundTheory.Global.valued_uniformizerUnit_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:21.744059+00:00
-- url     : https://prove2.me/submissions/067acf59-b013-4bf6-a6bf-4b0ca72064a7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
import Theorems.Thm_GroundTheory_Global_valued_of_irreducible


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
    Valued.v (((uniformizerUnit v ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
      exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, uniformizerUnit, Units.val_mk0,
    valued_of_irreducible v (irreducible_uniformizerAt v), ← exp_zsmul, smul_neg, zsmul_one,
    Int.cast_id]
end GroundTheory.Global
