-- Prove2me | solution 1 for GroundTheory.Global.idealIdele_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:24:02.645423+00:00
-- url     : https://prove2.me/submissions/b1eca96a-a085-4817-93c9-0de4818011a0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
import Theorems.Thm_GroundTheory_Global_count_eq_zero_of_not_mem_idealSupport
import Theorems.Thm_GroundTheory_Global_coe_prod_finiteSingleUnits_apply


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
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
namespace GroundTheory.Global
theorem _root_.solution (x : HeightOneSpectrum (𝓞 K)) :
    ((idealIdele I : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) x =
      ((uniformizerUnit x ^ FractionalIdeal.count K x (I : FractionalIdeal (𝓞 K)⁰ K) :
        (x.adicCompletion K)ˣ) : x.adicCompletion K) := by
  classical
  rw [idealIdele, coe_prod_finiteSingleUnits_apply]
  split_ifs with hx
  · rfl
  · rw [count_eq_zero_of_not_mem_idealSupport I hx, zpow_zero, Units.val_one]
end GroundTheory.Global
