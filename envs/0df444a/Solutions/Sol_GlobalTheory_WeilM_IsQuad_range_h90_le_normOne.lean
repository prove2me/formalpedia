-- Prove2me | solution 1 for GlobalTheory.WeilM.IsQuad.range_h90_le_normOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:46.014392+00:00
-- url     : https://prove2.me/submissions/2591b412-d28c-4e0b-8cfa-9989fbc9a591

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_mem_normOne
import Theorems.Thm_GlobalTheory_WeilM_hilbertNinetyQuotientHom_eq_iff
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_invol

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
namespace GlobalTheory.WeilM.IsQuad
theorem _root_.solution : (h90 c).range ≤ normOne c := by
  rintro u ⟨z, hz⟩
  have h1 := hilbertNinetyQuotientHom_eq_iff.mp hz
  have h2 := congrArg c h1
  rw [map_mul, h.invol] at h2
  refine mem_normOne.mpr (z.isUnit.mul_right_cancel ?_)
  rw [mul_assoc, h2, h1, one_mul]
end GlobalTheory.WeilM.IsQuad
