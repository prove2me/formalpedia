-- Prove2me | solution 1 for GlobalTheory.WeilM.IsQuad.h90_range_eq_normOne_of_isQuad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:10.003695+00:00
-- url     : https://prove2.me/submissions/4ac3aedd-3c8f-4584-b06a-02ef76d2ac41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_mem_normOne
import Theorems.Thm_GlobalTheory_WeilM_hilbertNinetyQuotientHom_eq_iff
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_exists_eq
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_algebraMap_injective
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_range_h90_le_normOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
namespace GlobalTheory.WeilM
namespace IsQuad
theorem _root_.solution {R : Type} [Field R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {ξ : E} (h : IsQuad c ξ) : (h90 c).range = normOne c := by
  refine le_antisymm h.range_h90_le_normOne fun u hu => ?_
  have hu := mem_normOne.mp hu
  obtain ⟨a, b, hab⟩ := h.exists_eq u
  have hc : c u = algebraMap R E a - algebraMap R E b * ξ := by rw [hab]; simp [h.anti, sub_eq_add_neg]
  by_cases ha : 1 + a = 0
  · have ha' : 1 + algebraMap R E a = 0 := by simpa using congrArg (algebraMap R E) ha
    have hb : algebraMap R E (b * b) * (ξ * ξ) = 0 := by
      rw [hc, hab] at hu
      rw [map_mul]
      linear_combination -hu + (algebraMap R E a - 1) * ha'
    have hb0 : b = 0 := mul_self_eq_zero.mp (h.algebraMap_injective (by
      rw [(h.unit.mul h.unit).mul_left_eq_zero.mp hb, map_zero]))
    refine ⟨h.unit.unit, hilbertNinetyQuotientHom_eq_iff.mpr ?_⟩
    rw [IsUnit.unit_spec, h.anti, hab, hb0, map_zero]
    linear_combination (-ξ) * ha'
  · have hz : IsUnit ((1 + (u : E)) * (1 + c u)) := by
      have : (1 + (u : E)) * (1 + c u) = algebraMap R E (2 * (1 + a)) := by
        rw [map_mul, map_add, map_one, map_ofNat]
        linear_combination hu + hab + hc
      rw [this]
      exact (Ne.isUnit (mul_ne_zero (Invertible.ne_zero 2) ha)).map _
    refine ⟨(isUnit_of_mul_isUnit_left hz).unit, hilbertNinetyQuotientHom_eq_iff.mpr ?_⟩
    rw [IsUnit.unit_spec, map_add, map_one]
    linear_combination hu
end IsQuad
end GlobalTheory.WeilM
