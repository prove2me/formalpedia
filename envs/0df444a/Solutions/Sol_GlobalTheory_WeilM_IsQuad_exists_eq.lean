-- Prove2me | solution 1 for GlobalTheory.WeilM.IsQuad.exists_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:29.685906+00:00
-- url     : https://prove2.me/submissions/225fa450-54a6-44ca-b33b-0f550db54bfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

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
theorem _root_.solution (z : E) : ∃ a b : R, z = algebraMap R E a + algebraMap R E b * ξ := by
  obtain ⟨b, h0, h1⟩ := h.basis
  refine ⟨b.repr z 0, b.repr z 1, ?_⟩
  conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one]
end GlobalTheory.WeilM.IsQuad
