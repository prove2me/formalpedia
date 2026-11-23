-- Prove2me | solution 1 for GlobalTheory.WeilM.IsQuad.algebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:45.2943+00:00
-- url     : https://prove2.me/submissions/a834080b-671e-4b4a-949d-3dfb09718acc

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
theorem _root_.solution : Function.Injective (algebraMap R E) := by
  obtain ⟨b, h0, -⟩ := h.basis
  intro x y hxy
  have : x • b 0 = y • b 0 := by rw [h0, Algebra.smul_def, Algebra.smul_def, hxy]
  simpa using congrArg (fun v => b.repr v 0) this
end GlobalTheory.WeilM.IsQuad
