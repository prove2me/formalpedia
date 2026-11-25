-- Prove2me | solution 1 for GroundTheory.LocalField.EqualChar.valuation_laurentHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:27.136358+00:00
-- url     : https://prove2.me/submissions/6f9dbf0f-4ee6-4616-9738-59f1532f724b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent
import Theorems.Thm_GroundTheory_LocalField_EqualChar_valuation_powerSeriesHom_of_constantCoeff_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries
open GroundTheory.LocalField.EqualChar
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
namespace GroundTheory.LocalField.EqualChar
theorem _root_.solution {x : 𝓀[K]⸨X⸩} (hx : x ≠ 0) :
    valuation K (laurentHom K p x) = valuation K (uniformizer K : K) ^ x.order := by
  conv_lhs => rw [← x.single_order_mul_powerSeriesPart]
  rw [map_mul, map_mul, laurentHom_single, map_zpow₀, laurentHom_coe,
    valuation_powerSeriesHom_of_constantCoeff_ne_zero K p, mul_one]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, LaurentSeries.powerSeriesPart_coeff,
    Nat.cast_zero, add_zero]
  exact fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)
end GroundTheory.LocalField.EqualChar
