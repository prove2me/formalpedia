-- Prove2me | solution 1 for GroundTheory.LocalField.EqualChar.valuation_powerSeriesHom_of_constantCoeff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:46:24.025886+00:00
-- url     : https://prove2.me/submissions/9d8acadd-6fef-4d54-9625-39daf4fdab8c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent
import Theorems.Thm_GroundTheory_LocalField_EqualChar_valuation_teichmullerHom
import Theorems.Thm_GroundTheory_LocalField_EqualChar_powerSeriesHom_C

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
theorem _root_.solution {F : PowerSeries 𝓀[K]}
    (hF : PowerSeries.constantCoeff F ≠ 0) : valuation K (powerSeriesHom K p F : K) = 1 := by
  set G : PowerSeries 𝓀[K] := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) F
  have hFG : F = PowerSeries.X * G + PowerSeries.C (PowerSeries.constantCoeff F) :=
    PowerSeries.eq_X_mul_shift_add_const F
  have h1 : valuation K (teichmullerHom K p (PowerSeries.constantCoeff F) : K) = 1 :=
    valuation_teichmullerHom K p hF
  have h2 : valuation K ((uniformizer K : K) * (powerSeriesHom K p G : K)) < 1 := by
    rw [map_mul]
    calc valuation K (uniformizer K : K) * valuation K (powerSeriesHom K p G : K)
        ≤ valuation K (uniformizer K : K) * 1 := by
          gcongr
          exact (Valuation.mem_integer_iff _ _).mp (powerSeriesHom K p G).2
      _ < 1 := by simpa using valuation_uniformizer_lt_one K
  rw [hFG, map_add, map_mul, powerSeriesHom_X, powerSeriesHom_C, Subring.coe_add,
    Subring.coe_mul, Valuation.map_add_eq_of_lt_right _ (h1 ▸ h2), h1]
end GroundTheory.LocalField.EqualChar
