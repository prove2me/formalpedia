-- Prove2me | solution 1 for GlobalTheory.WeilM.IsQuad.exists_unit_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:45.187665+00:00
-- url     : https://prove2.me/submissions/b26bf7d8-1486-416e-9e14-3224e30e4b92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_algebraMap_injective
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_exists_of_fixed

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
open GlobalTheory.WeilM.IsQuad
variable {ξ : E} (h : IsQuad c ξ)
include h
variable [Invertible (2 : R)]
namespace GlobalTheory.WeilM.IsQuad
theorem _root_.solution {z : Eˣ} (hz : c z = z) : ∃ a : Rˣ, z = Units.map (algebraMap R E : R →* E) a := by
  have hz' : c (z⁻¹ : Eˣ) = (z⁻¹ : Eˣ) := by
    refine z.isUnit.mul_left_cancel ?_
    conv_lhs => rw [← hz, ← map_mul]
    rw [Units.mul_inv, map_one]
  obtain ⟨a, ha⟩ := h.exists_of_fixed hz
  obtain ⟨a', ha'⟩ := h.exists_of_fixed hz'
  have : a * a' = 1 := h.algebraMap_injective (by rw [map_mul, ← ha, ← ha', Units.mul_inv, map_one])
  exact ⟨Units.mkOfMulEqOne a a' this, Units.ext ha⟩
end GlobalTheory.WeilM.IsQuad
