-- Prove2me | solution 1 for GlobalTheory.WeilM.IsQuad.exists_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:24.115081+00:00
-- url     : https://prove2.me/submissions/ec76c55a-2a3a-4c4c-993b-f414605fd3fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_exists_eq

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
theorem _root_.solution {z : E} (hz : c z = z) : ∃ a : R, z = algebraMap R E a := by
  obtain ⟨a, b, rfl⟩ := h.exists_eq z
  refine ⟨a, ?_⟩
  have h2 : algebraMap R E (⅟(2 : R)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap R E) 2, ← map_mul, invOf_mul_self, map_one]
  rw [map_add, map_mul, c.commutes, c.commutes, h.anti] at hz
  linear_combination (-algebraMap R E (⅟(2 : R))) * hz - algebraMap R E b * ξ * h2
end GlobalTheory.WeilM.IsQuad
