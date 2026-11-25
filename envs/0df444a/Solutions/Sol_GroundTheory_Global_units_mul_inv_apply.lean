-- Prove2me | solution 1 for GroundTheory.Global.units_mul_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:15:07.420001+00:00
-- url     : https://prove2.me/submissions/5a87ce8d-2bb4-464a-926c-ac62ae4e436b

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
theorem _root_.solution (u : (𝔸ᶠ[K])ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (u : 𝔸ᶠ[K]) v * ((u⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) v = 1 := by
  exact congrArg (fun a : 𝔸ᶠ[K] ↦ a v) u.mul_inv
end GroundTheory.Global
