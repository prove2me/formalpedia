-- Prove2me | solution 1 for GlobalTheory.WeilM.IsQuad.algebraMap_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:26.459953+00:00
-- url     : https://prove2.me/submissions/aac53134-14a7-4b62-bc9f-5d9707166ead

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_exists_eq
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
theorem _root_.solution (z : E) : algebraMap R E (Algebra.norm R z) = z * c z := by
  obtain ⟨x, y, rfl⟩ := h.exists_eq z
  obtain ⟨d, hd⟩ := h.exists_of_fixed (z := ξ * ξ) (by rw [map_mul, h.anti, neg_mul_neg])
  obtain ⟨b, h0, h1⟩ := h.basis
  have e0 : (algebraMap R E x + algebraMap R E y * ξ) * b 0 = x • b 0 + y • b 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def]; ring
  have e1 : (algebraMap R E x + algebraMap R E y * ξ) * b 1 = (y * d) • b 0 + x • b 1 := by
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, map_mul, ← hd]; ring
  rw [Algebra.norm_eq_matrix_det b, det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  simp [h.anti, ← hd]
  ring
end GlobalTheory.WeilM.IsQuad
