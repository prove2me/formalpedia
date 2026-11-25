-- Prove2me | solution 1 for GroundTheory.Global.SUnit.finrank_range_valuationVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:34.764414+00:00
-- url     : https://prove2.me/submissions/6adcaf72-111f-416f-9e4c-277356325c16

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnitsKernel
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Theorems.Thm_GroundTheory_Global_SUnit_valuationVector_comp_placeUnitsMap

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.SUnit
variable (S : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite S]
namespace GroundTheory.Global.SUnit
theorem _root_.solution :
    finrank ℤ (LinearMap.range (valuationVector S)) = Nat.card S := by
  have : Fintype S := Fintype.ofFinite S
  apply le_antisymm
  · calc finrank ℤ (LinearMap.range (valuationVector S)) ≤ finrank ℤ (S → ℤ) :=
          Submodule.finrank_le _
      _ = Nat.card S := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
  · have hinj : Function.Injective (valuationVector S ∘ₗ placeUnitsMap S) := by
      rw [valuationVector_comp_placeUnitsMap]
      intro c d hcd
      have hh : (-(classNumber K : ℤ)) ≠ 0 := by
        simpa using classNumber_ne_zero K
      exact smul_right_injective (S → ℤ) hh hcd
    calc Nat.card S = finrank ℤ (S → ℤ) := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
      _ = finrank ℤ (LinearMap.range (valuationVector S ∘ₗ placeUnitsMap S)) :=
          (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ finrank ℤ (LinearMap.range (valuationVector S)) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
end GroundTheory.Global.SUnit
