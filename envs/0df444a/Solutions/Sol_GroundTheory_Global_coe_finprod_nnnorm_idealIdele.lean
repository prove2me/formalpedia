-- Prove2me | solution 1 for GroundTheory.Global.coe_finprod_nnnorm_idealIdele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:02:27.386793+00:00
-- url     : https://prove2.me/submissions/2c5505c3-9e45-464c-bfa9-09eafc05f92b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
import Theorems.Thm_GroundTheory_Global_norm_uniformizerUnit_zpow
import Theorems.Thm_GroundTheory_Global_idealIdele_apply
import Theorems.Thm_GroundTheory_Global_absNorm_eq_finprod
import Theorems.Thm_GroundTheory_Global_coe_finprod_nnnorm


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
    ((∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((idealIdele I : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v‖₊ : ℝ≥0) : ℝ) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ)⁻¹ := by
  rw [coe_finprod_nnnorm, absNorm_eq_finprod, ← finprod_inv_distrib]
  refine finprod_congr fun v ↦ ?_
  rw [idealIdele_apply, norm_uniformizerUnit_zpow, zpow_neg]
end GroundTheory.Global
