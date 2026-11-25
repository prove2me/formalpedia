-- Prove2me | solution 1 for GroundTheory.Global.nnnorm_integerUnitsToUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:39:14.614263+00:00
-- url     : https://prove2.me/submissions/8998b6e2-f595-4231-b026-688e97d7aa5a

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletionIntegers K)ˣ) :
    ‖((integerUnitsToUnits v u : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖₊ = 1 := by
  have h := IdeleGroup.norm_eq_one_of_mul_eq_one (K := K) (v := v)
    (a := ((integerUnitsToUnits v u : (v.adicCompletion K)ˣ) : v.adicCompletion K))
    (b := ((integerUnitsToUnits v u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))
    (by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
    (u : v.adicCompletionIntegers K).2 ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) :
      v.adicCompletionIntegers K).2
  exact NNReal.eq h
end GroundTheory.Global
