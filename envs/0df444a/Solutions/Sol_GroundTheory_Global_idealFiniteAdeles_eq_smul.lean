-- Prove2me | solution 1 for GroundTheory.Global.idealFiniteAdeles_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:20.844836+00:00
-- url     : https://prove2.me/submissions/637607f9-2e9a-46c8-b662-a3c691374fd7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
import Theorems.Thm_GroundTheory_Global_inv_uniformizerUnit_zpow_mul_mem_iff
import Theorems.Thm_GroundTheory_Global_mem_units_smul_integralFiniteAdeles_iff
import Theorems.Thm_GroundTheory_Global_mem_idealFiniteAdeles
import Theorems.Thm_GroundTheory_Global_idealIdele_apply

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
theorem _root_.solution :
    (idealFiniteAdeles I : Set 𝔸ᶠ[K]) =
      idealIdele I • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) := by
  ext y
  rw [mem_units_smul_integralFiniteAdeles_iff, SetLike.mem_coe, mem_idealFiniteAdeles]
  refine forall_congr' fun v ↦ ?_
  rw [idealIdele_apply, inv_uniformizerUnit_zpow_mul_mem_iff]
end GroundTheory.Global
