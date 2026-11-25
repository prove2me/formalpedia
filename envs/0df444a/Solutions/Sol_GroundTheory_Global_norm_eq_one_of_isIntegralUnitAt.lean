-- Prove2me | solution 1 for GroundTheory.Global.norm_eq_one_of_isIntegralUnitAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:21:48.659034+00:00
-- url     : https://prove2.me/submissions/9798f054-5cd8-45a8-904e-d51c7de16c81

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Theorems.Thm_GroundTheory_Global_units_mul_inv_apply

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
theorem _root_.solution {u : (𝔸ᶠ[K])ˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h : IsIntegralUnitAt u v) : ‖(u : 𝔸ᶠ[K]) v‖ = 1 :=
  IdeleGroup.norm_eq_one_of_mul_eq_one (units_mul_inv_apply u v) h.1 h.2
end GroundTheory.Global
